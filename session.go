package sprites

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"time"
)

// SessionList represents a list of execution sessions
type SessionList struct {
	Sessions []Session `json:"sessions"`
}

// ListSessions retrieves a list of active sessions for a sprite
func (c *Client) ListSessions(ctx context.Context, spriteName string) ([]*Session, error) {
	// Build URL
	url := fmt.Sprintf("%s/v1/sprites/%s/exec", c.baseURL, spriteName)

	// Create request
	httpReq, err := http.NewRequestWithContext(ctx, "GET", url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))

	// Make request
	client := &http.Client{Timeout: 30 * time.Second}
	resp, err := client.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("failed to list sessions: %w", err)
	}
	defer resp.Body.Close()

	// Check status
	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	// Parse response
	var result map[string]interface{}
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	// Extract sessions array
	sessionsRaw, ok := result["sessions"].([]interface{})
	if !ok {
		// No sessions or invalid format
		return []*Session{}, nil
	}

	// Convert to Session structs
	sessions := make([]*Session, 0, len(sessionsRaw))
	for _, s := range sessionsRaw {
		if sessionMap, ok := s.(map[string]interface{}); ok {
			session := &Session{
				ID:      fmt.Sprintf("%v", sessionMap["id"]),
				Command: fmt.Sprintf("%v", sessionMap["command"]),
			}

			// Parse created time
			if created, ok := sessionMap["created"].(string); ok {
				if t, err := time.Parse(time.RFC3339, created); err == nil {
					session.Created = t
				}
			}

			// Parse activity data
			if bytesPerSec, ok := sessionMap["bytes_per_second"].(float64); ok {
				session.BytesPerSecond = bytesPerSec
			}
			if isActive, ok := sessionMap["is_active"].(bool); ok {
				session.IsActive = isActive
			}
			if lastActivity, ok := sessionMap["last_activity"].(string); ok {
				if t, err := time.Parse(time.RFC3339, lastActivity); err == nil {
					session.LastActivity = &t
				}
			}

			sessions = append(sessions, session)
		}
	}

	return sessions, nil
}

// ListSessions retrieves a list of active sessions for this sprite
func (s *Sprite) ListSessions(ctx context.Context) ([]*Session, error) {
	return s.client.ListSessions(ctx, s.name)
}

// AttachSession creates a new Cmd that attaches to an existing session
func (c *Client) AttachSession(spriteName string, sessionID string) *Cmd {
	return c.AttachSessionWithOrg(spriteName, sessionID, nil)
}

// AttachSessionWithOrg creates a new Cmd that attaches to an existing session with organization information
func (c *Client) AttachSessionWithOrg(spriteName string, sessionID string, org *OrganizationInfo) *Cmd {
	sprite := &Sprite{
		name:   spriteName,
		client: c,
		org:    org,
	}

	cmd := &Cmd{
		Path:   "tmux",
		Args:   []string{"tmux", "attach", "-t", sessionID},
		ctx:    context.Background(),
		sprite: sprite,
	}

	// Session attachment requires TTY
	cmd.tty = true

	// Set the session ID in the WebSocket URL parameters
	cmd.sessionID = sessionID

	return cmd
}

// AttachSession creates a new Cmd that attaches to an existing session
func (s *Sprite) AttachSession(sessionID string) *Cmd {
	return s.client.AttachSession(s.name, sessionID)
}

// AttachSessionContext creates a new Cmd with context that attaches to an existing session
func (c *Client) AttachSessionContext(ctx context.Context, spriteName string, sessionID string) *Cmd {
	cmd := c.AttachSession(spriteName, sessionID)
	cmd.ctx = ctx
	return cmd
}

// AttachSessionContext creates a new Cmd with context that attaches to an existing session
func (s *Sprite) AttachSessionContext(ctx context.Context, sessionID string) *Cmd {
	return s.client.AttachSessionContext(ctx, s.name, sessionID)
}

// Add sessionID field to Cmd struct (this would need to be added to exec.go)
// For now, we'll handle it in buildWebSocketURL by checking if it's a tmux attach command

// IsSessionActive returns true if the session has recent activity
func (s *Session) IsSessionActive() bool {
	if !s.IsActive {
		return false
	}
	if s.LastActivity == nil {
		return s.IsActive
	}
	// Consider a session active if there was activity in the last 5 minutes
	return time.Since(*s.LastActivity) < 5*time.Minute
}

// GetActivityAge returns how long ago the last activity was
func (s *Session) GetActivityAge() time.Duration {
	if s.LastActivity == nil {
		return time.Since(s.Created)
	}
	return time.Since(*s.LastActivity)
}
