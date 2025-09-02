package main

import (
	"context"
	"fmt"
	"log/slog"
	"net/url"
	"os"
	"time"

	"github.com/nshafer/phx"
	"github.com/superfly/sprite-env/server/api/handlers"
)

// Context key for storing admin channel data
type adminChannelContextKey struct{}

// AdminChannel manages the outbound Phoenix channel connection
type AdminChannel struct {
	url     string
	token   string
	socket  *phx.Socket
	channel *phx.Channel
	logger  *slog.Logger

	// Message queue for when channel is not ready
	messageQueue chan queuedMessage
	stopCh       chan struct{}
	ctx          context.Context
	cancel       context.CancelFunc
	readyCh      chan struct{} // Signals when channel becomes ready
}

type queuedMessage struct {
	eventType string
	payload   map[string]interface{}
}

// NewAdminChannel creates a new admin channel manager
func NewAdminChannel(logger *slog.Logger) *AdminChannel {
	channelURL := os.Getenv("SPRITE_ADMIN_CHANNEL")
	token := os.Getenv("SPRITE_HTTP_API_TOKEN")

	// Use default URL if not specified
	if channelURL == "" {
		channelURL = "https://api.sprites.dev/internal/admin"
	}

	if token == "" {
		// Return nil if not configured
		logger.Info("Admin channel disabled (no SPRITE_HTTP_API_TOKEN)")
		return nil
	}

	logger.Info("Admin channel configured", "base_url", channelURL)

	ctx, cancel := context.WithCancel(context.Background())
	ac := &AdminChannel{
		url:          channelURL,
		token:        token,
		logger:       logger,
		messageQueue: make(chan queuedMessage, 100),
		stopCh:       make(chan struct{}),
		ctx:          ctx,
		cancel:       cancel,
		readyCh:      make(chan struct{}),
	}

	// Start message queue processor
	go ac.processMessageQueue()

	return ac
}

// Start connects to the channel
func (ac *AdminChannel) Start() error {
	if ac == nil {
		return nil // Noop if not configured
	}

	// Parse the URL and add authentication parameters
	u, err := url.Parse(ac.url)
	if err != nil {
		return fmt.Errorf("invalid channel URL: %w", err)
	}

	// Add authentication parameters to the URL
	appName := os.Getenv("FLY_APP_NAME")
	q := u.Query()
	q.Set("authToken", ac.token)
	q.Set("appName", appName)
	u.RawQuery = q.Encode()

	// Log the configured URL and channel topic
	channelTopic := fmt.Sprintf("sprite:%s", appName)
	if appName == "" {
		channelTopic = "sprite:unknown"
	}
	ac.logger.Info("Starting admin channel",
		"url", u.String(),
		"topic", channelTopic,
		"app_name", appName)

	// Create socket with built-in reconnect configuration
	ac.socket = phx.NewSocket(u)
	ac.socket.Logger = &phxLogAdapter{logger: ac.logger}

	// Configure exponential backoff with max of 5 minutes
	ac.socket.ReconnectAfterFunc = func(tries int) time.Duration {
		backoff := time.Duration(1<<uint(tries)) * time.Second
		if backoff > 5*time.Minute {
			backoff = 5 * time.Minute
		}
		ac.logger.Debug("Reconnect attempt scheduled", "tries", tries, "backoff", backoff)
		return backoff
	}

	// Set up auto-reconnect on disconnect
	ac.socket.OnClose(func() {
		ac.logger.Debug("Socket disconnected, will auto-reconnect")
	})

	ac.socket.OnOpen(func() {
		ac.logger.Info("Socket connected")

		// Join (or rejoin) the admin channel with app-specific topic
		appName := os.Getenv("FLY_APP_NAME")
		if appName == "" {
			appName = "unknown"
		}
		channelTopic := fmt.Sprintf("sprite:%s", appName)
		if ac.channel == nil {
			ac.channel = ac.socket.Channel(channelTopic, nil)
		}
		if !ac.channel.IsJoined() {
			join, err := ac.channel.Join()
			if err != nil {
				ac.logger.Debug("error joining channel", "error", err)
				return
			}
			join.Receive("ok", func(response any) {
				ac.logger.Info("Joined admin channel", "topic", channelTopic)
				// Signal that channel is ready and flush queued messages
				select {
				case ac.readyCh <- struct{}{}:
				default:
					// Channel already signaled as ready
				}
				// Trigger flush of any queued messages
				ac.flushQueue()
			})
			join.Receive("error", func(response any) {
				ac.logger.Debug("Failed to join admin channel", "error", response)
			})
			join.Receive("timeout", func(response any) {
				ac.logger.Debug("Admin channel join timeout")
			})
		} else {
			// Channel was already joined, signal ready and flush
			ac.logger.Debug("Channel already joined, flushing queue")
			select {
			case ac.readyCh <- struct{}{}:
			default:
				// Channel already signaled as ready
			}
			ac.flushQueue()
		}
	})

	// Start connection in background goroutine so it doesn't block
	go func() {
		ac.logger.Debug("Attempting to connect to admin channel", "url", ac.url)
		if err := ac.socket.Connect(); err != nil {
			ac.logger.Debug("Failed to connect to admin channel", "error", err)
			// The socket will automatically retry with exponential backoff
		}
	}()

	// Return immediately - connection happens in background
	return nil
}

// Stop disconnects from the channel
func (ac *AdminChannel) Stop() error {
	if ac == nil {
		return nil
	}

	// Cancel context to stop message processor
	ac.cancel()

	// Leave channel and disconnect
	if ac.channel != nil {
		ac.channel.Leave()
	}

	if ac.socket != nil {
		ac.socket.Disconnect()
	}

	// Close stop channel to ensure processor exits
	close(ac.stopCh)

	ac.logger.Info("Admin channel stopped")

	return nil
}

// SendActivityEvent sends a simple activity event with a type and payload
func (ac *AdminChannel) SendActivityEvent(eventType string, payload map[string]interface{}) {
	if ac == nil {
		return
	}

	if payload == nil {
		payload = make(map[string]interface{})
	}

	// Queue the message - the processor will handle sending when ready
	select {
	case ac.messageQueue <- queuedMessage{eventType: eventType, payload: payload}:
		ac.logger.Debug("Queued activity event", "event", eventType)
	default:
		ac.logger.Debug("Message queue full, dropping activity event", "event", eventType)
	}
}

// processMessageQueue handles sending queued messages when channel is ready
func (ac *AdminChannel) processMessageQueue() {
	ticker := time.NewTicker(100 * time.Millisecond)
	defer ticker.Stop()

	for {
		select {
		case <-ac.ctx.Done():
			return
		case <-ac.stopCh:
			return
		case msg := <-ac.messageQueue:
			// Only send if channel is ready, otherwise re-queue
			if ac.IsReady() {
				_, err := ac.channel.Push(msg.eventType, msg.payload)
				if err != nil {
					// Best effort - just drop the message if it fails
					ac.logger.Debug("Failed to send activity event", "event", msg.eventType)
				}
			} else {
				// Channel not ready, try to re-queue but don't block
				select {
				case ac.messageQueue <- msg:
					// Successfully re-queued
				default:
					// Queue full, drop the message
				}
			}
		case <-ac.readyCh:
			// Channel became ready, flush any pending messages
			ac.flushQueue()
		case <-ticker.C:
			// Periodic check to flush queue if channel is ready
			if ac.IsReady() && len(ac.messageQueue) > 0 {
				ac.flushQueue()
			}
		}
	}
}

// flushQueue processes all queued messages when channel becomes ready
func (ac *AdminChannel) flushQueue() {
	if !ac.IsReady() {
		return
	}

	// Process all currently queued messages (non-blocking)
	count := len(ac.messageQueue)
	for i := 0; i < count; i++ {
		select {
		case msg := <-ac.messageQueue:
			// Best effort send - don't block or retry
			_, _ = ac.channel.Push(msg.eventType, msg.payload)
		default:
			// Queue is empty
			return
		}
	}
}

// EnrichContext adds the admin channel to the context
func (ac *AdminChannel) EnrichContext(ctx context.Context) context.Context {
	if ac == nil {
		return ctx
	}
	return context.WithValue(ctx, adminChannelContextKey{}, ac)
}

// RequestEnd notifies the channel when a request ends
func (ac *AdminChannel) RequestEnd(ctx context.Context, infoInterface interface{}) {
	if ac == nil || !ac.IsReady() {
		return // Noop if not configured or not ready
	}

	// Cast to the expected type
	info, ok := infoInterface.(*handlers.RequestInfo)
	if !ok {
		return // Silently ignore wrong type
	}

	// Check if this context has the admin channel
	if channel, ok := ctx.Value(adminChannelContextKey{}).(*AdminChannel); !ok || channel != ac {
		// Context doesn't have our channel, skip
		return
	}

	// Prepare the message
	payload := map[string]interface{}{
		"type":         "request_end",
		"request_type": info.RequestType,
		"request_id":   info.RequestID,
		"method":       info.Method,
		"path":         info.Path,
		"start_time":   info.StartTime.Unix(),
		"end_time":     info.EndTime.Unix(),
		"duration_ms":  info.DurationMS,
		"status_code":  info.StatusCode,
	}

	if info.Error != nil {
		payload["error"] = info.Error.Error()
	}

	if info.ExtraData != nil {
		for k, v := range info.ExtraData {
			payload[k] = v
		}
	}

	// Queue the message instead of sending directly - non-blocking
	select {
	case ac.messageQueue <- queuedMessage{eventType: "request_end", payload: payload}:
		// Successfully queued
	default:
		// Queue full, drop the message silently
	}
}

// GetFromContext retrieves the admin channel from context
func GetFromContext(ctx context.Context) *AdminChannel {
	if val := ctx.Value(adminChannelContextKey{}); val != nil {
		return val.(*AdminChannel)
	}
	return nil
}

// IsReady returns true if the admin channel is connected and joined
func (ac *AdminChannel) IsReady() bool {
	return ac != nil && ac.channel != nil && ac.channel.IsJoined()
}

// phxLogAdapter adapts slog.Logger to phx.Logger interface
type phxLogAdapter struct {
	logger *slog.Logger
}

func (l *phxLogAdapter) Print(level phx.LoggerLevel, kind string, v ...any) {
	msg := fmt.Sprint(v...)
	l.log(level, kind, msg)
}

func (l *phxLogAdapter) Println(level phx.LoggerLevel, kind string, v ...any) {
	msg := fmt.Sprintln(v...)
	l.log(level, kind, msg)
}

func (l *phxLogAdapter) Printf(level phx.LoggerLevel, kind string, format string, v ...any) {
	msg := fmt.Sprintf(format, v...)
	l.log(level, kind, msg)
}

func (l *phxLogAdapter) log(level phx.LoggerLevel, kind string, msg string) {
	switch level {
	case phx.LogDebug:
		// Skip DEBUG level logs to reduce noise
		return
	case phx.LogInfo:
		l.logger.Info(msg, "kind", kind)
	case phx.LogWarning:
		l.logger.Warn(msg, "kind", kind)
	case phx.LogError:
		l.logger.Error(msg, "kind", kind)
	default:
		l.logger.Info(msg, "kind", kind)
	}
}
