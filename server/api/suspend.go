package api

import (
	"context"
	"fmt"
	"net/http"
	"time"

	"github.com/superfly/sprite-env/pkg/fly"
)

func (h *Handlers) HandleSuspend(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	ctx, cancel := context.WithTimeout(r.Context(), 10*time.Second)
	defer cancel()

	start := time.Now()
	unfreezeFunc, err := h.system.SyncOverlay(ctx)
	if err != nil {
		h.logger.Debug("overlay sync error", "error", err)
	}
	// Defer unfreeze - this handler doesn't wait for resume, so unfreeze immediately
	defer func() {
		if err := unfreezeFunc(); err != nil {
			h.logger.Error("Failed to unfreeze filesystem", "error", err)
		}
	}()

	h.logger.Info(
		fmt.Sprintf(
			"Suspending, fs sync took %.2fs",
			time.Since(start).Seconds(),
		),
	)

	// Use fly package to suspend
	h.logger.Debug("calling fly suspend API")
	reqStart := time.Now()
	err = fly.Suspend(ctx)
	elapsed := time.Since(reqStart)

	if err != nil {
		h.logger.Debug("fly suspend call error", "error", err, "duration_s", elapsed.Seconds())
	} else {
		h.logger.Debug("fly suspend completed", "duration_s", elapsed.Seconds())
	}

	w.WriteHeader(http.StatusOK)
	fmt.Fprintf(w, "ok\n")
}
