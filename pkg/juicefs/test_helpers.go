package juicefs

import (
	"context"
	"testing"
	"time"
)

// CleanupTestJuiceFS unmounts JuiceFS and verifies cleanup
// Call this in a defer at the start of tests that manage mounts
func CleanupTestJuiceFS(t *testing.T, jfs *JuiceFS) {
	t.Helper()

	if jfs == nil {
		return
	}

	// Try to stop JuiceFS
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
	defer cancel()

	if err := jfs.Stop(ctx); err != nil {
		t.Logf("Stop error (may be expected): %v", err)
	}

	// Verify cleanup using the component's verifiers
	VerifyTestJuiceFSCleanup(t, jfs, ctx)
}

// VerifyTestJuiceFSCleanup verifies all resources are cleaned up using the component's verifiers
// This should be called after Stop() to ensure no resources leaked
func VerifyTestJuiceFSCleanup(t *testing.T, jfs *JuiceFS, ctx context.Context) {
	t.Helper()

	if jfs == nil {
		return
	}

	// Check channels are closed
	select {
	case <-jfs.stopCh:
	default:
		t.Errorf("CLEANUP FAILED: stopCh not closed")
	}
	select {
	case <-jfs.stoppedCh:
	default:
		t.Errorf("CLEANUP FAILED: stoppedCh not closed")
	}

	// Run all cleanup verifiers
	verifiers := jfs.CleanupVerifiers()
	for i, verify := range verifiers {
		if err := verify(ctx); err != nil {
			t.Errorf("CLEANUP VERIFICATION FAILED (verifier %d): %v", i, err)
		}
	}
}

// VerifyNoTestJuiceFS is deprecated - use VerifyTestJuiceFSCleanup instead
// Kept for backward compatibility with existing tests
func VerifyNoTestJuiceFS(t *testing.T, jfs *JuiceFS) {
	t.Helper()
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()
	VerifyTestJuiceFSCleanup(t, jfs, ctx)
}
