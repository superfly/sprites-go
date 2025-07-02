package config

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
)

// SpriteFile represents the contents of a .sprite file
type SpriteFile struct {
	Organization string `json:"organization"`
	Sprite       string `json:"sprite"`
}

// ReadSpriteFile reads the .sprite file from the current directory or parent directories
func ReadSpriteFile() (*SpriteFile, error) {
	dir, err := os.Getwd()
	if err != nil {
		return nil, err
	}

	// Look for .sprite file in current directory and parent directories
	for {
		spriteFile := filepath.Join(dir, ".sprite")
		if _, err := os.Stat(spriteFile); err == nil {
			// Found .sprite file
			data, err := os.ReadFile(spriteFile)
			if err != nil {
				return nil, fmt.Errorf("failed to read .sprite file: %w", err)
			}

			var sf SpriteFile
			if err := json.Unmarshal(data, &sf); err != nil {
				return nil, fmt.Errorf("failed to parse .sprite file: %w", err)
			}

			return &sf, nil
		}

		// Move to parent directory
		parent := filepath.Dir(dir)
		if parent == dir {
			// Reached root directory
			break
		}
		dir = parent
	}

	return nil, nil
}

// WriteSpriteFile writes a .sprite file in the current directory
func WriteSpriteFile(orgName, spriteName string) error {
	sf := SpriteFile{
		Organization: orgName,
		Sprite:       spriteName,
	}

	data, err := json.MarshalIndent(sf, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal sprite file: %w", err)
	}

	return os.WriteFile(".sprite", data, 0644)
}

// RemoveSpriteFile removes the .sprite file from the current directory
func RemoveSpriteFile() error {
	return os.Remove(".sprite")
}