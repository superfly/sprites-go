package main

import (
	"context"
	"fmt"
	"log/slog"
	"net/http"
	"net/url"
	"os"

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
}

// NewAdminChannel creates a new admin channel manager
func NewAdminChannel(logger *slog.Logger) *AdminChannel {
	channelURL := os.Getenv("SPRITE_ADMIN_CHANNEL")
	token := os.Getenv("SPRITE_TOKEN")

	if channelURL == "" || token == "" {
		// Return nil if not configured
		return nil
	}

	return &AdminChannel{
		url:    channelURL,
		token:  token,
		logger: logger,
	}
}

// Start connects to the channel
func (ac *AdminChannel) Start() error {
	if ac == nil {
		return nil // Noop if not configured
	}

	// Parse the URL
	u, err := url.Parse(ac.url)
	if err != nil {
		return fmt.Errorf("invalid channel URL: %w", err)
	}

	// Create socket with auth header
	ac.socket = phx.NewSocket(u)
	ac.socket.RequestHeader = http.Header{
		"Authorization": []string{"Bearer " + ac.token},
	}
	ac.socket.Logger = &phxLogAdapter{logger: ac.logger}

	// Set up auto-reconnect on disconnect
	ac.socket.OnClose(func() {
		ac.logger.Info("Socket disconnected, will auto-reconnect")
	})

	ac.socket.OnOpen(func() {
		ac.logger.Info("Socket connected")
		// Rejoin channel after reconnect
		if ac.channel != nil && !ac.channel.IsJoined() {
			if _, err := ac.channel.Join(); err != nil {
				ac.logger.Error("Failed to rejoin channel after reconnect", "error", err)
			}
		}
	})

	// Connect to the server
	if err := ac.socket.Connect(); err != nil {
		return fmt.Errorf("failed to connect to channel: %w", err)
	}

	// Create and join the channel
	channelTopic := "sprite:admin"
	ac.channel = ac.socket.Channel(channelTopic, nil)

	join, err := ac.channel.Join()
	if err != nil {
		ac.socket.Disconnect()
		return fmt.Errorf("failed to join channel: %w", err)
	}

	// Fire and forget - we don't wait for join confirmation
	join.Receive("ok", func(response any) {
		ac.logger.Info("Joined admin channel", "topic", channelTopic)
	})
	join.Receive("error", func(response any) {
		ac.logger.Warn("Failed to join admin channel", "error", response)
	})
	join.Receive("timeout", func(response any) {
		ac.logger.Warn("Admin channel join timeout")
	})

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

	ac.logger.Info("Admin channel stopped")

	return nil
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
		return // Noop if not configured or not connected
	}

	// Cast to the expected type
	info, ok := infoInterface.(*handlers.RequestInfo)
	if !ok {
		ac.logger.Error("RequestEnd called with wrong type", "type", fmt.Sprintf("%T", infoInterface))
		return
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

	// Send the message - fire and forget
	_, err := ac.channel.Push("request_end", payload)
	if err != nil {
		ac.logger.Debug("Failed to send request_end", "error", err)
		// Best effort - don't return error
	}
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
		l.logger.Debug(msg, "kind", kind)
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
