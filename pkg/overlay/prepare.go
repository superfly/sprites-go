package overlay

import (
	"context"
	"fmt"

	"github.com/superfly/sprite-env/pkg/checkpoint"
)

// PrepareCheckpoint returns a wrapper around next that prepares Manager
// and defers unfreeze on successful preparation.
func PrepareCheckpoint(om *Manager, next checkpoint.PrepFunc) checkpoint.PrepFunc {
	return func(ctx context.Context) (func() error, error) {
		if om != nil {
			if err := om.PrepareForCheckpoint(ctx); err != nil {
				return nil, fmt.Errorf("overlay prepare checkpoint: %w", err)
			}
		}

		nextResume, err := next(ctx)
		if err != nil {
			if om != nil {
				_ = om.UnfreezeAfterCheckpoint(ctx)
			}
			return nil, err
		}

		return func() error {
			var firstErr error
			if nextResume != nil {
				if e := nextResume(); e != nil && firstErr == nil {
					firstErr = e
				}
			}
			if om != nil {
				if e := om.UnfreezeAfterCheckpoint(ctx); e != nil && firstErr == nil {
					firstErr = e
				}
			}
			return firstErr
		}, nil
	}
}

// PrepareRestore ensures overlay is unmounted before restore and remounted after.
func PrepareRestore(om *Manager, next checkpoint.PrepFunc) checkpoint.PrepFunc {
	return func(ctx context.Context) (func() error, error) {
		if om != nil {
			// Best-effort sync/freeze/unfreeze to flush outstanding writes
			_ = om.PrepareForCheckpoint(ctx)
			_ = om.UnfreezeAfterCheckpoint(ctx)
			if err := om.Unmount(ctx); err != nil {
				return nil, fmt.Errorf("overlay unmount before restore: %w", err)
			}
		}

		nextResume, err := next(ctx)
		if err != nil {
			// Nothing to resume yet; overlay stays unmounted on error
			return nil, err
		}

		return func() error {
			var firstErr error
			if nextResume != nil {
				if e := nextResume(); e != nil && firstErr == nil {
					firstErr = e
				}
			}
			if om != nil {
				if e := om.Mount(ctx); e != nil && firstErr == nil {
					firstErr = e
				}
			}
			return firstErr
		}, nil
	}
}
