package overlay

import (
	"context"
	"errors"
	"testing"

	"github.com/superfly/sprite-env/pkg/checkpoint"
)

func TestPrepareCheckpoint(t *testing.T) {
	ctx := context.Background()

	t.Run("NilManager", func(t *testing.T) {
		var callCount int
		next := func(ctx context.Context) (func() error, error) {
			callCount++
			return func() error { return nil }, nil
		}

		prep := PrepareCheckpoint(nil, next)
		resume, err := prep(ctx)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		if callCount != 1 {
			t.Errorf("expected next to be called once, got %d", callCount)
		}
		if err := resume(); err != nil {
			t.Fatalf("resume error: %v", err)
		}
	})

	t.Run("NextError", func(t *testing.T) {
		nextErr := errors.New("next failed")
		next := func(ctx context.Context) (func() error, error) {
			return nil, nextErr
		}

		prep := PrepareCheckpoint(nil, next)
		_, err := prep(ctx)
		if err == nil {
			t.Fatal("expected error")
		}
		if !errors.Is(err, nextErr) {
			t.Errorf("expected next error, got: %v", err)
		}
	})
}

func TestPrepareRestore(t *testing.T) {
	ctx := context.Background()

	t.Run("NilManager", func(t *testing.T) {
		var callCount int
		next := func(ctx context.Context) (func() error, error) {
			callCount++
			return func() error { return nil }, nil
		}

		prep := PrepareRestore(nil, next)
		resume, err := prep(ctx)
		if err != nil {
			t.Fatalf("unexpected error: %v", err)
		}
		if callCount != 1 {
			t.Errorf("expected next to be called once, got %d", callCount)
		}
		if err := resume(); err != nil {
			t.Fatalf("resume error: %v", err)
		}
	})
}

func TestMiddlewareChaining(t *testing.T) {
	ctx := context.Background()

	// Test that PrepFunc can be chained properly
	var order []string

	// Create wrapper functions that track order
	wrapPrep := func(name string, next checkpoint.PrepFunc) checkpoint.PrepFunc {
		return func(ctx context.Context) (func() error, error) {
			order = append(order, name+"-prepare")

			nextResume, err := next(ctx)
			if err != nil {
				return nil, err
			}

			return func() error {
				// Call next resume first
				var firstErr error
				if nextResume != nil {
					firstErr = nextResume()
				}
				// Then do our cleanup
				order = append(order, name+"-resume")
				return firstErr
			}, nil
		}
	}

	// Base prep that records when it's called
	base := func(ctx context.Context) (func() error, error) {
		order = append(order, "base-prepare")
		return func() error {
			order = append(order, "base-resume")
			return nil
		}, nil
	}

	// Chain: m1 -> m2 -> base
	prep := wrapPrep("m1", wrapPrep("m2", base))

	// Execute prepare phase
	resume, err := prep(ctx)
	if err != nil {
		t.Fatalf("unexpected error: %v", err)
	}

	// Check prepare order (outer to inner)
	expectedPrepare := []string{"m1-prepare", "m2-prepare", "base-prepare"}
	if len(order) != 3 {
		t.Fatalf("expected 3 prepare calls, got %d: %v", len(order), order)
	}
	for i, expected := range expectedPrepare {
		if order[i] != expected {
			t.Errorf("prepare order[%d]: expected %s, got %s", i, expected, order[i])
		}
	}

	// Clear order for resume phase
	order = order[:0]

	// Execute resume phase
	if err := resume(); err != nil {
		t.Fatalf("resume error: %v", err)
	}

	// Check resume order (inner to outer - reverse of prepare)
	expectedResume := []string{"base-resume", "m2-resume", "m1-resume"}
	if len(order) != 3 {
		t.Fatalf("expected 3 resume calls, got %d: %v", len(order), order)
	}
	for i, expected := range expectedResume {
		if order[i] != expected {
			t.Errorf("resume order[%d]: expected %s, got %s", i, expected, order[i])
		}
	}
}
