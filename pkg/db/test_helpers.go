package db

import (
	"context"
	"testing"
	"time"
)

// CleanupTestDB performs shutdown and verification for tests
func CleanupTestDB(t *testing.T, m *Manager) {
	t.Helper()

	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
	defer cancel()

	if err := m.Stop(ctx); err != nil {
		t.Logf("Stop error (may be expected): %v", err)
	}

	VerifyTestDBCleanup(t, m, ctx)
}

// VerifyTestDBCleanup verifies all resources cleaned up
func VerifyTestDBCleanup(t *testing.T, m *Manager, ctx context.Context) {
	t.Helper()

	// Check that channels are closed
	select {
	case <-m.stopCh:
		// Good
	default:
		t.Errorf("CLEANUP FAILED: stopCh not closed")
	}

	select {
	case <-m.stoppedCh:
		// Good
	default:
		t.Errorf("CLEANUP FAILED: stoppedCh not closed")
	}

	// Run all cleanup verifiers
	verifiers := m.CleanupVerifiers()
	for i, verify := range verifiers {
		if err := verify(ctx); err != nil {
			t.Errorf("CLEANUP VERIFICATION FAILED (verifier %d): %v", i, err)
		}
	}
}
