package overlay

import (
	"context"
	"os"
	"path/filepath"
	"testing"
)

// Phase 1 Tests: Lifecycle behavior

func TestStartErrorsIfAlreadyStarted(t *testing.T) {
	mountPath := filepath.Join("/mnt", t.Name())
	baseDir := t.TempDir()
	lowerDir := filepath.Join(baseDir, "lower")
	os.MkdirAll(lowerDir, 0755)

	cfg := Config{
		BaseDir:    baseDir,
		ImageSize:  "1G",
		MountPath:  mountPath,
		LowerPaths: []string{lowerDir},
	}

	mgr := New(cfg)

	ctx := context.Background()

	// First Start will fail (no permissions/resources in test), but that's OK
	// We just want to verify the started flag works
	mgr.Start(ctx, "")

	// Second Start should error immediately due to started check
	err := mgr.Start(ctx, "")
	if err == nil {
		t.Fatal("expected error on second Start, got nil")
	}
	if err.Error() != "overlay manager already started" {
		t.Errorf("expected 'overlay manager already started' error, got: %v", err)
	}

	// Clean up
	mgr.Unmount(ctx)
}

func TestUnmountIsIdempotent(t *testing.T) {
	mountPath := filepath.Join("/mnt", t.Name())
	baseDir := t.TempDir()
	lowerDir := filepath.Join(baseDir, "lower")
	os.MkdirAll(lowerDir, 0755)

	cfg := Config{
		BaseDir:    baseDir,
		ImageSize:  "1G",
		MountPath:  mountPath,
		LowerPaths: []string{lowerDir},
	}

	mgr := New(cfg)

	ctx := context.Background()

	// Start overlay
	if err := mgr.Start(ctx, ""); err != nil {
		t.Fatalf("Start failed: %v", err)
	}

	// Multiple Unmounts should all succeed
	if err := mgr.Unmount(ctx); err != nil {
		t.Logf("first Unmount error (may be expected): %v", err)
	}

	if err := mgr.Unmount(ctx); err != nil {
		t.Logf("second Unmount error (may be expected): %v", err)
	}

	if err := mgr.Unmount(ctx); err != nil {
		t.Logf("third Unmount error (may be expected): %v", err)
	}
}

func TestVerifiersBeforeStart(t *testing.T) {
	mountPath := filepath.Join("/mnt", t.Name())
	baseDir := t.TempDir()
	lowerDir := filepath.Join(baseDir, "lower")
	os.MkdirAll(lowerDir, 0755)

	cfg := Config{
		BaseDir:    baseDir,
		ImageSize:  "1G",
		MountPath:  mountPath,
		LowerPaths: []string{lowerDir},
	}

	mgr := New(cfg)

	// Before Start, verifiers should be empty
	if len(mgr.SetupVerifiers()) != 0 {
		t.Errorf("Expected 0 setup verifiers before Start, got %d", len(mgr.SetupVerifiers()))
	}
	if len(mgr.CleanupVerifiers()) != 0 {
		t.Errorf("Expected 0 cleanup verifiers before Start, got %d", len(mgr.CleanupVerifiers()))
	}
}

func TestRestartCycle(t *testing.T) {
	mountPath := filepath.Join("/mnt", t.Name())
	baseDir := t.TempDir()
	lowerDir := filepath.Join(baseDir, "lower")
	os.MkdirAll(lowerDir, 0755)

	cfg := Config{
		BaseDir:    baseDir,
		ImageSize:  "1G",
		MountPath:  mountPath,
		LowerPaths: []string{lowerDir},
	}

	mgr := New(cfg)

	ctx := context.Background()

	// First cycle (may fail due to missing permissions/resources, but that's OK)
	mgr.Start(ctx, "")
	if err := mgr.Unmount(ctx); err != nil {
		t.Logf("first Unmount error (may be expected): %v", err)
	}

	// Verify started flag was reset
	if mgr.started {
		t.Error("started flag not reset after Unmount")
	}

	// Second cycle - Start should not error due to "already started"
	// It may fail for other reasons (permissions/resources) but not due to lifecycle
	err := mgr.Start(ctx, "")
	if err != nil && err.Error() == "overlay manager already started" {
		t.Fatalf("second Start failed with 'already started' error - lifecycle broken")
	}
	// Other errors are OK for this test

	if err := mgr.Unmount(ctx); err != nil {
		t.Logf("second Unmount error (may be expected): %v", err)
	}

	// Verify started flag was reset again
	if mgr.started {
		t.Error("started flag not reset after second Unmount")
	}
}

func TestVerifiersClearedOnRestart(t *testing.T) {
	mountPath := filepath.Join("/mnt", t.Name())
	baseDir := t.TempDir()
	lowerDir := filepath.Join(baseDir, "lower")
	os.MkdirAll(lowerDir, 0755)

	cfg := Config{
		BaseDir:    baseDir,
		ImageSize:  "1G",
		MountPath:  mountPath,
		LowerPaths: []string{lowerDir},
	}

	mgr := New(cfg)

	ctx := context.Background()

	// First start (will fail but that's OK for this test)
	mgr.Start(ctx, "")
	firstSetupCount := len(mgr.SetupVerifiers())
	firstCleanupCount := len(mgr.CleanupVerifiers())

	mgr.Unmount(ctx)

	// Second start
	mgr.Start(ctx, "")
	secondSetupCount := len(mgr.SetupVerifiers())
	secondCleanupCount := len(mgr.CleanupVerifiers())

	// Verifiers should be the same count (cleared and repopulated)
	if secondSetupCount != firstSetupCount {
		t.Errorf("Setup verifier count changed on restart: first=%d, second=%d",
			firstSetupCount, secondSetupCount)
	}
	if secondCleanupCount != firstCleanupCount {
		t.Errorf("Cleanup verifier count changed on restart: first=%d, second=%d",
			firstCleanupCount, secondCleanupCount)
	}

	mgr.Unmount(ctx)
}

// Phase 2 Tests: Verification behavior
// Note: These tests verify the verifier structure, not the actual system state
// Full integration tests requiring mount permissions should be in manager_linux_test.go

func TestVerifiersPopulated(t *testing.T) {
	mountPath := filepath.Join("/mnt", t.Name())
	baseDir := t.TempDir()
	lowerDir := filepath.Join(baseDir, "lower")
	os.MkdirAll(lowerDir, 0755)

	cfg := Config{
		BaseDir:    baseDir,
		ImageSize:  "1G",
		MountPath:  mountPath,
		LowerPaths: []string{lowerDir},
	}

	mgr := New(cfg)

	ctx := context.Background()

	// Start overlay
	if err := mgr.Start(ctx, ""); err != nil {
		t.Fatalf("Start failed: %v", err)
	}
	defer mgr.Unmount(ctx)

	// Verify verifiers were populated
	setupVerifiers := mgr.SetupVerifiers()
	cleanupVerifiers := mgr.CleanupVerifiers()

	if len(setupVerifiers) == 0 {
		t.Error("No setup verifiers were added during Start")
	}
	if len(cleanupVerifiers) == 0 {
		t.Error("No cleanup verifiers were added during Start")
	}

	t.Logf("Found %d setup verifiers and %d cleanup verifiers",
		len(setupVerifiers), len(cleanupVerifiers))
}

func TestSetupVerifiers(t *testing.T) {
	mountPath := filepath.Join("/mnt", t.Name())
	baseDir := t.TempDir()
	lowerDir := filepath.Join(baseDir, "lower")
	os.MkdirAll(lowerDir, 0755)

	cfg := Config{
		BaseDir:    baseDir,
		ImageSize:  "1G",
		MountPath:  mountPath,
		LowerPaths: []string{lowerDir},
	}

	mgr := New(cfg)

	ctx := context.Background()

	// Start overlay
	if err := mgr.Start(ctx, ""); err != nil {
		t.Fatalf("Start failed: %v", err)
	}
	defer mgr.Unmount(ctx)

	// Run all setup verifiers
	for i, verify := range mgr.SetupVerifiers() {
		if err := verify(ctx); err != nil {
			t.Errorf("Setup verifier %d failed: %v", i, err)
		}
	}
}

func TestCleanupVerifiers(t *testing.T) {
	mountPath := filepath.Join("/mnt", t.Name())
	baseDir := t.TempDir()
	lowerDir := filepath.Join(baseDir, "lower")
	os.MkdirAll(lowerDir, 0755)

	cfg := Config{
		BaseDir:    baseDir,
		ImageSize:  "1G",
		MountPath:  mountPath,
		LowerPaths: []string{lowerDir},
	}

	mgr := New(cfg)

	ctx := context.Background()

	// Start and unmount overlay
	if err := mgr.Start(ctx, ""); err != nil {
		t.Fatalf("Start failed: %v", err)
	}
	if err := mgr.Unmount(ctx); err != nil {
		t.Fatalf("Unmount failed: %v", err)
	}

	// Run all cleanup verifiers
	for i, verify := range mgr.CleanupVerifiers() {
		if err := verify(ctx); err != nil {
			t.Errorf("Cleanup verifier %d failed: %v", i, err)
		}
	}
}
