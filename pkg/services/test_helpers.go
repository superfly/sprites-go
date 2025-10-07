package services

import (
	"context"
	"testing"
	"time"
)

// CleanupTestServices performs cleanup and verification for test services manager
func CleanupTestServices(t *testing.T, m *Manager) {
	t.Helper()

	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	if err := m.Stop(ctx); err != nil {
		t.Logf("Stop error (may be expected): %v", err)
	}

	VerifyTestServicesCleanup(t, m, ctx)
}

// VerifyTestServicesCleanup verifies all resources are cleaned up
func VerifyTestServicesCleanup(t *testing.T, m *Manager, ctx context.Context) {
	t.Helper()

	// Check channels are closed
	select {
	case <-m.stopCh:
	default:
		t.Errorf("CLEANUP FAILED: stopCh not closed")
	}
	select {
	case <-m.stoppedCh:
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
