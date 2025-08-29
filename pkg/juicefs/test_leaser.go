//go:build test
// +build test

package juicefs

import "context"

// testLeaser is a no-op LeaseManager implementation used in unit tests.
// It pretends to acquire the lease immediately and tracks the number of times
// Wait is called so tests can verify slow-start behaviour if needed.
type testLeaser struct {
	attempts int
}

// newTestLeaser returns a LeaseManager suitable for injecting into JuiceFS
// configuration inside unit tests.
func newTestLeaser() LeaseManager {
	return &testLeaser{}
}

// Wait pretends to acquire the lease instantly.
func (t *testLeaser) Wait(ctx context.Context) error {
	t.attempts++
	return nil
}

// LeaseAttemptCount returns how many times Wait has been called.
func (t *testLeaser) LeaseAttemptCount() int {
	return t.attempts
}

// Stop is a no-op for the test leaser.
func (t *testLeaser) Stop() {}
