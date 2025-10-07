package leaser

import (
	"context"
	"testing"
	"time"
)

// CleanupTestLeaser performs shutdown and verification for tests
func CleanupTestLeaser(t *testing.T, l *Leaser) {
	t.Helper()

	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	if err := l.Stop(ctx); err != nil {
		t.Logf("Stop error (may be expected): %v", err)
	}

	VerifyTestLeaserCleanup(t, l, ctx)
}

// VerifyTestLeaserCleanup verifies all resources cleaned up
func VerifyTestLeaserCleanup(t *testing.T, l *Leaser, ctx context.Context) {
	t.Helper()

	// Check that channels are closed
	select {
	case <-l.stopCh:
		// Good
	default:
		t.Errorf("CLEANUP FAILED: stopCh not closed")
	}

	select {
	case <-l.stoppedCh:
		// Good
	default:
		t.Errorf("CLEANUP FAILED: stoppedCh not closed")
	}

	// Run all cleanup verifiers
	verifiers := l.CleanupVerifiers()
	for i, verify := range verifiers {
		if err := verify(ctx); err != nil {
			t.Errorf("CLEANUP VERIFICATION FAILED (verifier %d): %v", i, err)
		}
	}
}
