package juicefs

import (
	"context"
	"errors"
	"testing"

	"github.com/superfly/sprite-env/pkg/overlay"
)

func TestPrepareCheckpoint(t *testing.T) {
	// Test that it's a proper no-op wrapper
	called := false
	inner := func(ctx context.Context) (func() error, error) {
		called = true
		return func() error { return nil }, nil
	}

	wrapped := PrepareCheckpoint(inner)
	resume, err := wrapped(context.Background())
	if err != nil {
		t.Fatal(err)
	}
	if !called {
		t.Fatal("inner function not called")
	}
	if err := resume(); err != nil {
		t.Fatal(err)
	}
}

func TestPrepareRestore(t *testing.T) {
	// Test that it's a proper no-op wrapper
	called := false
	inner := func(ctx context.Context) (func() error, error) {
		called = true
		return func() error { return nil }, nil
	}

	wrapped := PrepareRestore(inner)
	resume, err := wrapped(context.Background())
	if err != nil {
		t.Fatal(err)
	}
	if !called {
		t.Fatal("inner function not called")
	}
	if err := resume(); err != nil {
		t.Fatal(err)
	}
}

func TestPreparePassesErrors(t *testing.T) {
	// Test that errors are passed through
	expectedErr := errors.New("test error")
	inner := func(ctx context.Context) (func() error, error) {
		return nil, expectedErr
	}

	wrapped := PrepareCheckpoint(inner)
	_, err := wrapped(context.Background())
	if err != expectedErr {
		t.Fatalf("expected %v, got %v", expectedErr, err)
	}
}

func TestPrepareWithOverlayNoOp(t *testing.T) {
	// Integration test showing it works with overlay.NoopPrep
	noop := overlay.NoopPrep()
	wrapped := PrepareCheckpoint(noop)

	resume, err := wrapped(context.Background())
	if err != nil {
		t.Fatal(err)
	}
	if err := resume(); err != nil {
		t.Fatal(err)
	}
}
