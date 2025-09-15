package handlers

import (
	"context"
	"fmt"
	"net"
	"net/http"
	"os"
	"time"
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

	app := os.Getenv("FLY_APP_NAME")
	mid := os.Getenv("FLY_MACHINE_ID")
	url := fmt.Sprintf(
		"http://flaps/v1/apps/%s/machines/%s/suspend",
		app, mid,
	)

	d := &net.Dialer{}
	tr := &http.Transport{
		DialContext: func(c context.Context, network, addr string) (net.Conn, error) {
			return d.DialContext(c, "unix", "/.fly/api")
		},
	}
	client := &http.Client{Transport: tr}

	req, _ := http.NewRequestWithContext(ctx, http.MethodPost, url, nil)
	h.logger.Debug("flaps suspend request", "url", url, "socket", "/.fly/api")
	reqStart := time.Now()
	resp, err := client.Do(req)
	elapsed := time.Since(reqStart)
	if err != nil {
		h.logger.Debug("flaps suspend call error", "error", err)
	} else if resp != nil {
		h.logger.Debug(
			"flaps suspend response",
			"status", resp.StatusCode,
			"duration_s", elapsed.Seconds(),
		)
		if resp.Body != nil {
			resp.Body.Close()
		}
	}

	w.WriteHeader(http.StatusOK)
	fmt.Fprintf(w, "ok\n")
}
