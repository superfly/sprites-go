package main

import (
	"context"
	"fmt"
	"log/slog"
	"net/url"
	"os"

	"github.com/superfly/sprite-env/pkg/phx"
	"github.com/superfly/sprite-env/pkg/tap"
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
}

// NewAdminChannel creates a new admin channel manager
func NewAdminChannel(ctx context.Context) *AdminChannel {
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
	}

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

	// Create socket with default reconnect configuration
	ac.socket = phx.NewSocket(u)
	ac.socket.Logger = &phxLogAdapter{logger: ac.logger}

	// Start connection (non-blocking, starts background goroutines)
	if err := ac.socket.Connect(); err != nil {
		return fmt.Errorf("failed to start connection: %w", err)
	}

	// Create and join channel immediately - no need to wait for socket connection
	ac.channel = ac.socket.Channel(channelTopic, nil)

	// Set up ping/pong handler
	ac.channel.On("ping", func(payload any) {
		// Simply echo back the payload as pong
		ac.channel.Push("pong", payload)
	})

	// Handle sprite_assigned notifications
	ac.channel.On("sprite_assigned", func(payload any) {
		if data, ok := payload.(map[string]interface{}); ok {
			ac.logger.Info("Sprite assigned",
				"org_id", data["org_id"],
				"sprite_name", data["sprite_name"],
				"sprite_id", data["sprite_id"],
				"app_name", data["app_name"])
		} else {
			ac.logger.Info("Sprite assigned", "payload", payload)
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
	})

	join.Receive("error", func(reason any) {
		ac.logger.Error("Failed to join admin channel",
			"topic", channelTopic,
			"reason", reason)
	})

	join.Receive("timeout", func(response any) {
		ac.logger.Warn("Admin channel join timed out",
			"topic", channelTopic,
			"response", response)
	})

	// Return immediately - connection and join happen asynchronously
	return nil
}

// Stop disconnects from the channel
func (ac *AdminChannel) Stop() error {
	if ac == nil {
		return nil
	}

	// Leave channel and disconnect
	if ac.channel != nil {
		ac.channel.Leave()
	}

	if ac.socket != nil {
		ac.socket.Disconnect()
	}

	return nil
}

// SendActivityEvent sends a simple activity event with a type and payload
func (ac *AdminChannel) SendActivityEvent(eventType string, payload map[string]interface{}) {
	if ac == nil {
		// This shouldn't happen if admin channel is properly initialized
		return
	}

	if ac.channel == nil {
		ac.logger.Warn("Admin channel not connected, cannot send event", "event_type", eventType)
		return
	}

	if payload == nil {
		payload = make(map[string]interface{})
	}

	// Log the event being sent
	ac.logger.Debug("Sending admin channel event",
		"event_type", eventType,
		"payload", payload,
		"channel_joined", ac.channel.IsJoined(),
		"channel_joining", ac.channel.IsJoining(),
		"socket_connected", ac.socket != nil && ac.socket.IsConnected())

	// Send the event - Phoenix library will queue if not joined and flush when joined
	_, err := ac.channel.Push(eventType, payload)
	if err != nil {
		ac.logger.Error("Failed to push admin channel event",
			"event_type", eventType,
			"error", err)
		return
	}

	// These are fire-and-forget events, no need to handle responses or timeouts
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
	if ac == nil || ac.channel == nil {
		return // Noop if not configured or channel not created
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

	// Send directly - Phoenix library handles queueing
	ac.channel.Push("request_end", payload)
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
