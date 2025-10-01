package checkpoint

import "context"

// NoopPrep returns a PrepFunc that does nothing and resumes with no-op.
func NoopPrep() PrepFunc {
	return func(ctx context.Context) (func() error, error) {
		return func() error { return nil }, nil
	}
}
