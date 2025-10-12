package system

import (
	"context"
	"database/sql"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"time"

	_ "github.com/mattn/go-sqlite3"
)

// SpriteInfo holds the sprite assignment information
type SpriteInfo struct {
	SpriteName string    `json:"sprite_name"`
	SpriteURL  string    `json:"sprite_url"`
	OrgID      string    `json:"org_id"`
	SpriteID   string    `json:"sprite_id"`
	AssignedAt time.Time `json:"assigned_at"`
}

// InitializeSpriteDB creates the sprite database and table if they don't exist
func (s *System) InitializeSpriteDB(ctx context.Context) error {
	dbPath := s.GetSpriteDBPath()

	db, err := sql.Open("sqlite3", dbPath)
	if err != nil {
		return fmt.Errorf("failed to open sprite database: %w", err)
	}
	defer db.Close()

	// Create table with single-row constraint
	_, err = db.ExecContext(ctx, `
		CREATE TABLE IF NOT EXISTS sprite_info (
			id INTEGER PRIMARY KEY CHECK (id = 1),
			sprite_name TEXT NOT NULL,
			sprite_url TEXT NOT NULL,
			org_id TEXT NOT NULL,
			sprite_id TEXT NOT NULL,
			assigned_at TIMESTAMP NOT NULL
		)
	`)
	if err != nil {
		return fmt.Errorf("failed to create sprite_info table: %w", err)
	}

	s.logger.Info("Sprite database initialized", "path", dbPath)
	return nil
}

// GetSpriteDBPath returns the path to the sprite database
func (s *System) GetSpriteDBPath() string {
	return filepath.Join(s.config.WriteDir, "sprite.db")
}

// GetSpriteInfo retrieves the sprite assignment information
// Returns an error if the sprite has not been assigned yet
func (s *System) GetSpriteInfo(ctx context.Context) (*SpriteInfo, error) {
	dbPath := s.GetSpriteDBPath()

	db, err := sql.Open("sqlite3", dbPath)
	if err != nil {
		return nil, fmt.Errorf("failed to open sprite database: %w", err)
	}
	defer db.Close()

	var info SpriteInfo
	err = db.QueryRowContext(ctx, `
		SELECT sprite_name, sprite_url, org_id, sprite_id, assigned_at
		FROM sprite_info
		WHERE id = 1
	`).Scan(&info.SpriteName, &info.SpriteURL, &info.OrgID, &info.SpriteID, &info.AssignedAt)

	if err == sql.ErrNoRows {
		return nil, fmt.Errorf("sprite not assigned")
	}
	if err != nil {
		return nil, fmt.Errorf("failed to query sprite info: %w", err)
	}

	return &info, nil
}

// SetSpriteInfo sets the sprite assignment information
// If sprite is already assigned:
// - sprite_name, org_id, and sprite_id cannot be changed (returns error)
// - sprite_url can be updated
func (s *System) SetSpriteInfo(ctx context.Context, info *SpriteInfo) error {
	dbPath := s.GetSpriteDBPath()

	db, err := sql.Open("sqlite3", dbPath)
	if err != nil {
		return fmt.Errorf("failed to open sprite database: %w", err)
	}
	defer db.Close()

	// Check if already assigned
	var existing SpriteInfo
	err = db.QueryRowContext(ctx, `
		SELECT sprite_name, sprite_url, org_id, sprite_id, assigned_at
		FROM sprite_info
		WHERE id = 1
	`).Scan(&existing.SpriteName, &existing.SpriteURL, &existing.OrgID, &existing.SpriteID, &existing.AssignedAt)

	if err == sql.ErrNoRows {
		// Not yet assigned - do initial insert
		_, err = db.ExecContext(ctx, `
			INSERT INTO sprite_info (id, sprite_name, sprite_url, org_id, sprite_id, assigned_at)
			VALUES (1, ?, ?, ?, ?, ?)
		`, info.SpriteName, info.SpriteURL, info.OrgID, info.SpriteID, info.AssignedAt)

		if err != nil {
			return fmt.Errorf("failed to insert sprite info: %w", err)
		}

		s.logger.Info("Sprite assignment stored",
			"sprite_name", info.SpriteName,
			"sprite_url", info.SpriteURL,
			"org_id", info.OrgID,
			"sprite_id", info.SpriteID)

		return nil
	}

	if err != nil {
		return fmt.Errorf("failed to check assignment status: %w", err)
	}

	// Already assigned - check if immutable fields are being changed
	if info.SpriteName != existing.SpriteName || info.OrgID != existing.OrgID || info.SpriteID != existing.SpriteID {
		return fmt.Errorf("sprite name and org cannot be changed once set")
	}

	// URL can be updated
	if info.SpriteURL != existing.SpriteURL {
		_, err = db.ExecContext(ctx, `
			UPDATE sprite_info
			SET sprite_url = ?
			WHERE id = 1
		`, info.SpriteURL)

		if err != nil {
			return fmt.Errorf("failed to update sprite url: %w", err)
		}

		s.logger.Info("Sprite URL updated",
			"sprite_name", info.SpriteName,
			"old_url", existing.SpriteURL,
			"new_url", info.SpriteURL)
	}

	return nil
}

// ApplySpriteHostname applies the sprite hostname to the container
// This sets the hostname in the container's UTS namespace and updates /etc/hosts and /etc/hostname in the overlay
func (s *System) ApplySpriteHostname(ctx context.Context, spriteName, spriteURL string) error {
	// Update /etc/hosts in the overlayfs
	// /mnt/newroot is the overlay that becomes the container's root filesystem
	// Note: We only add the short hostname to /etc/hosts, not the sprite URL
	// The sprite URL is a public DNS name and shouldn't be in /etc/hosts
	// Keep "sprite" as an alias for backwards compatibility
	hostsEntry := fmt.Sprintf(`# IPv4
127.0.0.1   localhost
127.0.0.1   sprite
127.0.0.1   %s

# IPv6
fdf::1      localhost
fdf::1      sprite
fdf::1      %s

`, spriteName, spriteName)

	hostsPath := "/mnt/newroot/etc/hosts"
	if err := writeHostsFile(hostsPath, []byte(hostsEntry), 0644); err != nil {
		return fmt.Errorf("failed to write container hosts file: %w", err)
	}
	s.logger.Info("Updated container hosts file", "path", hostsPath, "sprite_name", spriteName, "sprite_url", spriteURL)

	// Write /etc/hostname to persist the short hostname across reboots
	// The container will automatically apply this hostname when it starts
	hostnamePath := "/mnt/newroot/etc/hostname"
	if err := writeHostsFile(hostnamePath, []byte(spriteName+"\n"), 0644); err != nil {
		return fmt.Errorf("failed to write container hostname file: %w", err)
	}
	s.logger.Info("Updated container hostname file", "path", hostnamePath, "sprite_name", spriteName)

	// Set the hostname in the container's UTS namespace if container is running
	if err := setContainerHostname(spriteName); err != nil {
		s.logger.Warn("Failed to set container hostname (container may not be running yet)", "error", err)
		// Don't return error - hostname will be set when container starts from /etc/hostname
	} else {
		s.logger.Info("Set container hostname", "hostname", spriteName)
	}

	return nil
}

// SpriteEnvironmentResponse is the response from setting sprite environment
type SpriteEnvironmentResponse struct {
	Status     string `json:"status"`
	Message    string `json:"message,omitempty"`
	SpriteName string `json:"sprite_name,omitempty"`
	SpriteURL  string `json:"sprite_url,omitempty"`
}

// SetSpriteEnvironment is the high-level method that stores sprite info and applies hostname
// Takes an interface{} to avoid import cycles (can be *SpriteInfo or any struct with matching fields)
func (s *System) SetSpriteEnvironment(ctx context.Context, infoAny interface{}) (interface{}, error) {
	// Convert to SpriteInfo using JSON round-trip (handles any struct with matching json tags)
	data, err := json.Marshal(infoAny)
	if err != nil {
		return nil, fmt.Errorf("invalid sprite info format: %w", err)
	}

	var info SpriteInfo
	if err := json.Unmarshal(data, &info); err != nil {
		return nil, fmt.Errorf("invalid sprite info fields: %w", err)
	}

	// Set timestamp if not provided
	if info.AssignedAt.IsZero() {
		info.AssignedAt = time.Now().UTC()
	}

	// Store in database (will error if already assigned)
	if err := s.SetSpriteInfo(ctx, &info); err != nil {
		return nil, err
	}

	// Apply hostname to container
	if err := s.ApplySpriteHostname(ctx, info.SpriteName, info.SpriteURL); err != nil {
		return nil, err
	}

	s.logger.Info("Sprite environment configured successfully",
		"sprite_name", info.SpriteName,
		"sprite_url", info.SpriteURL)

	return &SpriteEnvironmentResponse{
		Status:     "ok",
		Message:    "sprite environment configured",
		SpriteName: info.SpriteName,
		SpriteURL:  info.SpriteURL,
	}, nil
}

// writeHostsFile writes content to a file path
// This is a helper to allow testing without actually modifying system files
var writeHostsFile = func(path string, data []byte, perm uint32) error {
	// In production, this writes to the actual filesystem
	// In tests, this can be mocked
	return os.WriteFile(path, data, os.FileMode(perm))
}
