package main

import (
	"log/slog"
	"os"
	"testing"
	"time"
)

// This test exercises the AdminChannel against a staging endpoint.
// It does not assert on remote behavior; it only verifies that our
// code paths (Start/SendActivityEvent/Stop) execute without panic.
func TestAdminChannel_StagingConnection(t *testing.T) {
	os.Setenv("SPRITE_ADMIN_CHANNEL", "wss://sprites-api-staging.fly.dev/internal/sprites/sprite-env-prime/admin")
	os.Setenv("SPRITE_TOKEN", "asdfasdfjkml")

	ac := NewAdminChannel(slog.Default())
	if ac == nil {
		t.Fatalf("AdminChannel was nil; expected configured instance")
	}

	if err := ac.Start(); err != nil {
		// Do not fail the test on connection errors; just log for visibility
		t.Logf("Start returned error: %v", err)
	} else {
		t.Logf("AdminChannel started")
	}

	// Give the socket a brief moment to attempt connect/join
	time.Sleep(500 * time.Millisecond)

	// Send a simple activity event
	ac.SendActivityEvent("test", map[string]interface{}{"from": "unit_test"})
	t.Logf("Pushed activity event: test")

	if err := ac.Stop(); err != nil {
		t.Logf("Stop returned error: %v", err)
	} else {
		t.Logf("AdminChannel stopped")
	}
}

// Using slog.Default for logging in tests
