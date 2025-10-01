package main

import (
	"log"
	"os"
	"testing"
)

// Global shared sprite for all tests
var sharedSpriteName string

// TestMain handles setup and teardown for all tests
func TestMain(m *testing.M) {
	// Check if we have the required environment variable
	if os.Getenv("SPRITES_TEST_TOKEN") == "" {
		os.Exit(0) // Skip tests if no token is provided
	}

	// Create a single sprite for all tests
	baseURL := getBaseURL()
	testCliPath := getTestCliPathForSetup()
	spriteName := getTestSpriteNameForSetup()

	log.Printf("Creating shared test sprite: %s\n", spriteName)
	err := createSprite(testCliPath, baseURL, spriteName)
	if err != nil {
		log.Fatalf("Failed to create shared test sprite: %v", err)
	}

	sharedSpriteName = spriteName
	log.Printf("Shared test sprite created: %s\n", sharedSpriteName)

	// Warm up the sprite with a simple command to ensure it's fully ready
	log.Printf("Warming up sprite...\n")
	err = warmupSprite(testCliPath, baseURL, spriteName)
	if err != nil {
		log.Printf("Warning: sprite warmup failed: %v (continuing anyway)", err)
	} else {
		log.Printf("Sprite warmup completed\n")
	}

	// Run all tests
	code := m.Run()

	// Clean up the sprite
	log.Printf("Destroying shared test sprite: %s\n", sharedSpriteName)
	err = destroySprite(testCliPath, baseURL, sharedSpriteName)
	if err != nil {
		log.Printf("Warning: failed to destroy shared test sprite: %v", err)
	}

	// Exit with the same code as the tests
	os.Exit(code)
}
