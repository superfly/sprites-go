package sprites

import (
	"context"
	"time"
)

// OrganizationInfo represents organization information attached to a sprite
type OrganizationInfo struct {
	Name string
	URL  string
}

// Sprite represents a sprite instance.
type Sprite struct {
	name   string
	client *Client
	org    *OrganizationInfo

	// Additional fields from API responses
	ID               string
	OrganizationName string
	Status           string
	Config           *SpriteConfig
	Environment      map[string]string
	CreatedAt        time.Time
	UpdatedAt        time.Time
	BucketName       string
	PrimaryRegion    string
	URL              string
	URLSettings      *URLSettings

	// Transport selection for this sprite: "control" or "endpoint"
	transport      string
	controlChecked bool
	lastProbeErr   error
}

// Name returns the sprite's name.
func (s *Sprite) Name() string {
	return s.name
}

// Client returns the client associated with this sprite.
func (s *Sprite) Client() *Client {
	return s.client
}

// Organization returns the organization information associated with this sprite.
func (s *Sprite) Organization() *OrganizationInfo {
	return s.org
}

// Destroy destroys the sprite.
func (s *Sprite) Destroy() error {
	return s.Delete(context.Background())
}

// ensureControlSupport checks if the sprite supports control connections
// This is called lazily on first exec/proxy operation
func (s *Sprite) ensureControlSupport(ctx context.Context) {
	if s.controlChecked {
		return
	}
	_ = s.probeControlSupport(ctx)
}

// probeControlSupport performs a synchronous control probe and records the outcome.
// Returns errControlBadGateway when the sprite is unavailable (502) so callers can surface it.
func (s *Sprite) probeControlSupport(ctx context.Context) error {
	if s.controlChecked {
		return s.lastProbeErr
	}
	s.controlChecked = true

	// Try to establish a control connection to test support
	pool := s.client.getOrCreatePool(s.name)
	if url, err := pool.buildControlURL(); err == nil {
		dbg("sprites: attempting control connect", "sprite", s.name, "url", url.String())
	} else {
		dbg("sprites: control url build failed", "sprite", s.name, "err", err)
	}
	conn, err := pool.dial(ctx)
	if err != nil {
		switch err {
		case errControlNotFound:
			// 404: control not available, use EndpointAPI
			dbg("sprites: control not available (404)", "sprite", s.name)
			s.transport = "endpoint"
			s.lastProbeErr = nil
			return nil
		case errControlBadGateway:
			// 502: sprite does not exist/reachable; surface this as an error to caller
			// Store a sentinel by marking checked but unsupported and attach the error on client for retrieval
			dbg("sprites: control probe 502 (sprite missing)", "sprite", s.name)
			// Use panic+recover at call sites would be bad; instead store state to force immediate error on first op
			s.transport = "endpoint"
			s.lastProbeErr = errControlBadGateway
			return s.lastProbeErr
		default:
			// Other errors: leave unknown, operations will retry and bubble errors
			dbg("sprites: control probe error (non-404); leaving support unknown", "sprite", s.name, "err", err)
			// Default to endpoint to avoid surprising dials; operations may still work
			s.transport = "endpoint"
			s.lastProbeErr = nil
			return nil
		}
	}

	// Success - control connections are supported
	s.transport = "control"
	dbg("sprites: control supported", "sprite", s.name)
	s.lastProbeErr = nil

	// Add this initial connection to the pool
	conn.mu.Lock()
	conn.busy = false
	conn.mu.Unlock()

	// Add the connection to the pool
	pool.mu.Lock()
	pool.conns = append(pool.conns, conn)
	pool.mu.Unlock()
	return nil
}
