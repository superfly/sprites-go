package system

import (
	"context"
	"encoding/json"
	"fmt"
	"log/slog"
	"net/url"
	"os"
	"reflect"

	"github.com/superfly/sprite-env/pkg/phx"
	"github.com/superfly/sprite-env/pkg/tap"
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
	system  *System // Reference to system for handling sprite assignment
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
		ac.handleSpriteAssigned(payload)
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

	// Leave channel and disconnect
	if ac.channel != nil {
		ac.channel.Leave()
	}

	if ac.socket != nil {
		ac.socket.Disconnect()
	}

	return nil
}

// Push sends a message to the admin channel with automatic nil checking and payload conversion.
// It accepts any payload type and will convert it to map[string]interface{} via JSON marshaling if needed.
// This is safe to call even if the admin channel is nil or not connected.
func (ac *AdminChannel) Push(eventType string, payload interface{}) {
	if ac == nil {
		// Silently return if admin channel is not configured
		return
	}

	if ac.channel == nil {
		// Silently return if channel is not connected
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

	// Send the event - Phoenix library will queue if not joined and flush when joined
	_, err := ac.channel.Push(eventType, mapPayload)

	if err != nil && ac.logger != nil {
		ac.logger.Error("Failed to push admin channel event",
			"event_type", eventType,
			"error", err)
	}
}

// SendActivityEvent sends a simple activity event with a type and payload
func (ac *AdminChannel) SendActivityEvent(eventType string, payload map[string]interface{}) {
	if ac == nil {
		// This shouldn't happen, but let's check
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

	// Use the new Push method
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

// SetSystem sets the system reference for the admin channel
// This is called after the system is fully initialized
func (ac *AdminChannel) SetSystem(system *System) {
	if ac != nil {
		ac.system = system
	}
}

// handleSpriteAssigned processes sprite_assigned events from the admin channel
func (ac *AdminChannel) handleSpriteAssigned(payload any) {
	// Hand off to system for processing (it will handle deserialization)
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

	// Reply with the exact same response structure
	ac.replyToSpriteAssigned(response)
}

// replyToSpriteAssigned sends a reply to the sprite_assigned event
func (ac *AdminChannel) replyToSpriteAssigned(response interface{}) {
	if ac.channel == nil {
		return
	}

	ac.channel.Push("sprite_assigned_reply", response)
}
