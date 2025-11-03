package system

import (
	"context"
	"encoding/json"
	"fmt"
	"log/slog"
	"net/url"
	"os"
	"reflect"
	"sync"

	"github.com/superfly/sprite-env/pkg/phx"
	"github.com/superfly/sprite-env/pkg/tap"
)

// Context key for storing admin channel data
type adminChannelContextKey struct{}

// pendingEvent represents an event waiting to be sent
type pendingEvent struct {
	eventType string
	payload   map[string]interface{}
}

// AdminChannel manages the outbound Phoenix channel connection
type AdminChannel struct {
	url     string
	token   string
	socket  *phx.Socket
	channel *phx.Channel
	logger  *slog.Logger
	env     Environment
	system  *System // Reference to system for handling sprite assignment

	// Run loop infrastructure
	eventCh          chan pendingEvent
	done             chan struct{}
	connReady        chan bool
	channelReady     chan bool
	pendingEvents    []pendingEvent
	isSocketConnected bool
	isChannelJoined   bool
	stopOnce         sync.Once // Ensures Stop() only closes done channel once
}

// NewAdminChannel creates a new admin channel manager
func NewAdminChannel(ctx context.Context, env Environment) *AdminChannel {
	logger := tap.Logger(ctx)
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

	ac := &AdminChannel{
		url:    channelURL,
		token:  token,
		logger: logger,
		env:    env,
	}

	return ac
}

// Start connects to the channel
func (ac *AdminChannel) Start() error {
	// No-op if no token configured
	if ac.token == "" {
		return nil
	}

	// Allow tests to disable admin channel
	if os.Getenv("SPRITE_DISABLE_ADMIN_CHANNEL") == "true" {
		ac.logger.Info("Admin channel disabled by environment variable")
		return nil
	}

	// Parse the URL and add authentication parameters
	u, err := url.Parse(ac.url)
	if err != nil {
		return fmt.Errorf("invalid channel URL: %w", err)
	}

	// Add authentication parameters to the URL
	appName := ac.env.AppName()
	q := u.Query()
	q.Set("authToken", ac.token)
	q.Set("appName", appName)
	u.RawQuery = q.Encode()

	// Log the configured URL and channel topic
	channelTopic := fmt.Sprintf("sprite:%s", appName)
	if appName == "" {
		channelTopic = "sprite:unknown"
	}

	// Create a sanitized URL for logging (without auth token)
	sanitizedURL := *u
	sanitizedQuery := sanitizedURL.Query()
	if sanitizedQuery.Has("authToken") {
		sanitizedQuery.Set("authToken", "[REDACTED]")
		sanitizedURL.RawQuery = sanitizedQuery.Encode()
	}

	ac.logger.Info("Starting admin channel",
		"url", sanitizedURL.String(),
		"topic", channelTopic,
		"app_name", appName)

	// Create socket with default reconnect configuration
	ac.socket = phx.NewSocket(u)

	// Use NoopLogger during tests to reduce log spam
	if os.Getenv("SPRITE_TEST_QUIET_PHX") == "true" {
		ac.socket.Logger = phx.NewNoopLogger()
	} else {
		ac.socket.Logger = &phxLogAdapter{logger: ac.logger}
	}

	// Initialize run loop infrastructure
	ac.eventCh = make(chan pendingEvent, 100)
	ac.done = make(chan struct{})
	ac.connReady = make(chan bool, 10)
	ac.channelReady = make(chan bool, 10)
	ac.pendingEvents = make([]pendingEvent, 0)
	ac.isSocketConnected = false
	ac.isChannelJoined = false

	// Start connection (non-blocking, starts background goroutines)
	if err := ac.socket.Connect(); err != nil {
		return fmt.Errorf("failed to start connection: %w", err)
	}

	// Register socket callbacks to track connection state
	ac.socket.OnOpen(func() {
		select {
		case ac.connReady <- true:
		default:
		}
	})
	ac.socket.OnClose(func() {
		select {
		case ac.connReady <- false:
		default:
		}
	})
	ac.socket.OnError(func(err error) {
		select {
		case ac.connReady <- false:
		default:
		}
	})

	// Create and join channel immediately - no need to wait for socket connection
	ac.channel = ac.socket.Channel(channelTopic, nil)

	// Set up ping/pong handler (no message ID checking needed for ping/pong)
	ac.channel.On("ping", func(payload any) {
		// Simply echo back the payload as pong
		ac.channel.Push("pong", payload)
	})

	// Handle sprite_assigned notifications
	ac.channel.On("sprite_assigned", func(payload any) {
		ac.handleSpriteAssigned(payload, true)
	})

	// Register channel callbacks to track join state
	ac.channel.On("phx_join", func(payload any) {
		select {
		case ac.channelReady <- true:
		default:
		}
	})
	ac.channel.On("phx_close", func(payload any) {
		select {
		case ac.channelReady <- false:
		default:
		}
	})
	ac.channel.On("phx_error", func(payload any) {
		select {
		case ac.channelReady <- false:
		default:
		}
	})

	// Join the channel - it will wait for socket connection if needed
	ac.logger.Debug("Attempting to join admin channel", "topic", channelTopic)

	join, err := ac.channel.Join()
	if err != nil {
		return fmt.Errorf("failed to join channel: %w", err)
	}

	// Set up callbacks to track join status
	join.Receive("ok", func(response any) {
		ac.logger.Info("Successfully joined admin channel",
			"topic", channelTopic,
			"response", response)

		// Signal channel ready (phx_join event should also fire, but signal here too for safety)
		select {
		case ac.channelReady <- true:
		default:
		}

		// Apply any sprite assignment info included in the join reply (no reply push)
		ac.handleSpriteAssigned(response, false)
	})

	join.Receive("error", func(reason any) {
		ac.logger.Error("Failed to join admin channel",
			"topic", channelTopic,
			"reason", reason)
		// Signal channel not ready
		select {
		case ac.channelReady <- false:
		default:
		}
	})

	join.Receive("timeout", func(response any) {
		ac.logger.Warn("Admin channel join timed out",
			"topic", channelTopic,
			"response", response)
		// Signal channel not ready
		select {
		case ac.channelReady <- false:
		default:
		}
	})

	// Launch run loop goroutine
	go ac.run()

	// Return immediately - connection and join happen asynchronously
	return nil
}

// run is the main event loop for AdminChannel
func (ac *AdminChannel) run() {
	for {
		select {
		case <-ac.done:
			// Shutdown signal received, exit gracefully
			return

		case ready := <-ac.connReady:
			// Socket connection state changed
			ac.isSocketConnected = ready
			// Channel will auto-rejoin via phx library's rejoin timer when socket reconnects

		case joined := <-ac.channelReady:
			// Channel join state changed
			ac.isChannelJoined = joined
			if joined {
				// Channel just joined, flush pending events
				var failedEvents []pendingEvent
				for _, event := range ac.pendingEvents {
					_, err := ac.channel.Push(event.eventType, event.payload)
					if err != nil {
						// Re-queue for retry later
						failedEvents = append(failedEvents, event)
					}
				}
				// Keep only failed events
				ac.pendingEvents = failedEvents
			}

		case event := <-ac.eventCh:
			// New event to send
			if ac.isSocketConnected && ac.isChannelJoined {
				// Ready to send immediately
				_, err := ac.channel.Push(event.eventType, event.payload)
				if err != nil {
					// Push failed, queue for retry
					ac.pendingEvents = append(ac.pendingEvents, event)
				}
			} else {
				// Not ready, queue for later
				ac.pendingEvents = append(ac.pendingEvents, event)
			}
		}
	}
}

// Stop disconnects from the channel
func (ac *AdminChannel) Stop() error {
	// Signal run loop to shutdown (only once)
	ac.stopOnce.Do(func() {
		if ac.done != nil {
			close(ac.done)
		}
	})

	// Disconnect socket immediately
	if ac.socket != nil {
		ac.socket.Disconnect()
	}

	return nil
}

// LeaveAsync initiates a channel leave without waiting for any response.
// Errors and timeouts are ignored; shutdown proceeds regardless.
func (ac *AdminChannel) LeaveAsync() {
	if ac == nil || ac.channel == nil {
		return
	}
	go func() {
		_, _ = ac.channel.Leave()
	}()
}

// Push sends a message to the admin channel with automatic nil checking and payload conversion.
// It accepts any payload type and will convert it to map[string]interface{} via JSON marshaling if needed.
// This is safe to call even if the admin channel is nil or not connected.
// Push is fully async and never blocks - it sends to the event queue and returns immediately.
func (ac *AdminChannel) Push(eventType string, payload interface{}) {
	if ac == nil {
		// Silently return if admin channel is not configured
		return
	}

	if ac.eventCh == nil {
		// Not started yet or already stopped
		return
	}

	// Convert payload to map[string]interface{} if needed
	var mapPayload map[string]interface{}

	if payload == nil {
		mapPayload = make(map[string]interface{})
	} else if m, ok := payload.(map[string]interface{}); ok {
		// Already a map, use it directly
		mapPayload = m
	} else {
		// Convert via JSON marshaling
		data, err := json.Marshal(payload)
		if err != nil {
			if ac.logger != nil {
				ac.logger.Error("Failed to marshal payload for admin channel",
					"event_type", eventType,
					"error", err)
			}
			return
		}

		if err := json.Unmarshal(data, &mapPayload); err != nil {
			if ac.logger != nil {
				ac.logger.Error("Failed to unmarshal payload for admin channel",
					"event_type", eventType,
					"error", err)
			}
			return
		}
	}

	// Send to event queue (non-blocking)
	event := pendingEvent{
		eventType: eventType,
		payload:   mapPayload,
	}
	select {
	case ac.eventCh <- event:
		// Successfully queued
	default:
		// Channel full (shouldn't happen with size 100, but handle gracefully)
		if ac.logger != nil {
			ac.logger.Error("Admin channel event queue full, dropping event",
				"event_type", eventType)
		}
	}
}

// SendActivityEvent sends a simple activity event with a type and payload.
// This is a convenience wrapper around Push() for activity events.
func (ac *AdminChannel) SendActivityEvent(eventType string, payload map[string]interface{}) {
	ac.Push(eventType, payload)
}

// EnrichContext adds the admin channel to the context
func (ac *AdminChannel) EnrichContext(ctx context.Context) context.Context {
	return context.WithValue(ctx, adminChannelContextKey{}, ac)
}

// RequestEnd notifies the channel when a request ends
func (ac *AdminChannel) RequestEnd(ctx context.Context, infoInterface interface{}) {
	if ac.channel == nil {
		return // No-op if channel not created
	}

	// Check if this context has the admin channel
	if channel, ok := ctx.Value(adminChannelContextKey{}).(*AdminChannel); !ok || channel != ac {
		// Context doesn't have our channel, skip
		return
	}

	// Use reflection to extract fields (avoids import cycle with api package)
	v := reflect.ValueOf(infoInterface)
	if v.Kind() == reflect.Ptr {
		v = v.Elem()
	}
	if v.Kind() != reflect.Struct {
		return // Not a struct
	}

	// Build payload from struct fields
	payload := make(map[string]interface{})
	t := v.Type()
	for i := 0; i < v.NumField(); i++ {
		field := t.Field(i)
		value := v.Field(i)
		// Convert field name to snake_case for JSON
		if field.IsExported() && value.CanInterface() {
			payload[field.Name] = value.Interface()
		}
	}
	payload["type"] = "request_end"

	// Send via async Push
	ac.Push("request_end", payload)
}

// GetFromContext retrieves the admin channel from context
func GetFromContext(ctx context.Context) *AdminChannel {
	if val := ctx.Value(adminChannelContextKey{}); val != nil {
		return val.(*AdminChannel)
	}
	return nil
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

// SetSystem sets the system reference for the admin channel
// This is called after the system is fully initialized
func (ac *AdminChannel) SetSystem(system *System) {
	if ac != nil {
		ac.system = system
	}
}

// handleSpriteAssigned processes sprite_assigned events
func (ac *AdminChannel) handleSpriteAssigned(payload any, sendReply bool) {
	// Convert payload to map for logging
	data, ok := payload.(map[string]interface{})
	if ok {
		ac.logger.Debug("Sprite assigned",
			"org_id", data["org_id"],
			"sprite_name", data["sprite_name"],
			"sprite_id", data["sprite_id"])
	} else {
		ac.logger.Debug("Sprite assigned", "payload", payload)
	}

	// Hand off to system for processing
	if ac.system == nil {
		ac.logger.Error("System not available for sprite assignment")
		ac.replyToSpriteAssigned(map[string]string{
			"status":  "error",
			"message": "system not initialized",
		})
		return
	}

	ctx := context.Background()
	response, err := ac.system.SetSpriteEnvironment(ctx, payload)
	if err != nil {
		ac.replyToSpriteAssigned(map[string]string{
			"status":  "error",
			"message": err.Error(),
		})
		return
	}

	// Reply with the exact same response structure (only for inbound events)
	if sendReply {
		ac.replyToSpriteAssigned(response)
	}
}

// replyToSpriteAssigned sends a reply to the sprite_assigned event
func (ac *AdminChannel) replyToSpriteAssigned(response interface{}) {
	ac.Push("sprite_assigned_reply", response)
}
