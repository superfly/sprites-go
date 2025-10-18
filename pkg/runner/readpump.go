package runner

import (
	"context"
	"io"
)

// StartReadPump copies from src to dst until src returns EOF, an error, or ctx is canceled.
// On EOF from src, it forwards EOF to the child by closing dst. On ctx cancel, it also closes dst
// to unblock the child. The returned channel is closed when the pump goroutine exits.
//
// Notes:
//   - There is no way to forcibly unblock a generic src.Read; on cancellation we close dst and
//     allow the goroutine to finish on its own when src yields. This avoids data races and keeps
//     the contract simple and predictable.
func StartReadPump(ctx context.Context, src io.Reader, dst io.WriteCloser) <-chan struct{} {
	done := make(chan struct{})
	go func() {
		defer close(done)

		buf := make([]byte, 32*1024)
		for {
			// Opportunistically check for cancellation between iterations
			select {
			case <-ctx.Done():
				_ = dst.Close()
				return
			default:
			}

			n, rerr := src.Read(buf)
			if n > 0 {
				// Write all read bytes
				written := 0
				for written < n {
					m, werr := dst.Write(buf[written:n])
					if werr != nil {
						// Close to signal EOF to child on writer error
						_ = dst.Close()
						return
					}
					written += m
				}
			}

			if rerr != nil {
				if rerr == io.EOF {
					// Forward EOF to the child
					_ = dst.Close()
					return
				}
				// On read error (non-EOF), close writer and exit
				_ = dst.Close()
				return
			}
		}
	}()
	return done
}
