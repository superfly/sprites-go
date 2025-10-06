package juicefs

import (
	"context"
	"testing"
)

// Phase 1 Tests: Lifecycle behavior

func TestStartErrorsIfAlreadyStarted(t *testing.T) {
	cfg := Config{
		BaseDir:    t.TempDir(),
		LocalMode:  true,
		VolumeName: "test",
	}

	jfs, err := New(cfg)
	if err != nil {
		t.Fatal(err)
	}

	ctx := context.Background()

	// First Start will fail (no juicefs binary in test), but that's OK
	// We just want to verify the started flag works
	jfs.Start(ctx)

	// Second Start should error immediately due to started check
	err = jfs.Start(ctx)
	if err == nil {
		t.Fatal("expected error on second Start, got nil")
	}
	if err.Error() != "juicefs already started" {
		t.Errorf("expected 'juicefs already started' error, got: %v", err)
	}

	// Clean up
	jfs.Stop(ctx)
}

func TestStopIsIdempotent(t *testing.T) {
	cfg := Config{
		BaseDir:    t.TempDir(),
		LocalMode:  true,
		VolumeName: "test",
	}

	jfs, err := New(cfg)
	if err != nil {
		t.Fatal(err)
	}

	ctx := context.Background()

	// Start in background
	go jfs.Start(ctx)

	// Multiple Stops should all succeed
	if err := jfs.Stop(ctx); err != nil {
		t.Fatalf("first Stop failed: %v", err)
	}

	if err := jfs.Stop(ctx); err != nil {
		t.Fatalf("second Stop failed: %v", err)
	}

	if err := jfs.Stop(ctx); err != nil {
		t.Fatalf("third Stop failed: %v", err)
	}
}

func TestChannelsClosed(t *testing.T) {
	cfg := Config{
		BaseDir:    t.TempDir(),
		LocalMode:  true,
		VolumeName: "test",
	}

	jfs, err := New(cfg)
	if err != nil {
		t.Fatal(err)
	}

	ctx := context.Background()

	// Start (will fail but that's OK)
	jfs.Start(ctx)

	// Stop and wait for completion
	if err := jfs.Stop(ctx); err != nil {
		t.Fatal(err)
	}

	// Check stopCh is closed
	select {
	case <-jfs.stopCh:
		// Good
	default:
		t.Error("stopCh not closed after Stop")
	}

	// Check stoppedCh is closed
	select {
	case <-jfs.stoppedCh:
		// Good
	default:
		t.Error("stoppedCh not closed after Stop")
	}
}

func TestVerifiersBeforeStart(t *testing.T) {
	cfg := Config{
		BaseDir:    t.TempDir(),
		LocalMode:  true,
		VolumeName: "test",
	}

	jfs, err := New(cfg)
	if err != nil {
		t.Fatal(err)
	}

	// Before Start, verifiers should be empty
	if len(jfs.SetupVerifiers()) != 0 {
		t.Errorf("Expected 0 setup verifiers before Start, got %d", len(jfs.SetupVerifiers()))
	}
	if len(jfs.CleanupVerifiers()) != 0 {
		t.Errorf("Expected 0 cleanup verifiers before Start, got %d", len(jfs.CleanupVerifiers()))
	}
}
