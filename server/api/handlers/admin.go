package handlers

import (
	"fmt"
	"net/http"
)

// HandleAdminResetState handles admin reset-state requests
// This stops the process, clears the JuiceFS active and checkpoints directories,
// and removes the checkpoint DB. The process can be started again after reset.
func (h *Handlers) HandleAdminResetState(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	h.logger.Info("Admin reset-state request received")

	// Stop the process if it's running
	if h.system.IsProcessRunning() {
		h.logger.Info("Stopping process for reset-state")
		if err := h.system.StopProcess(); err != nil {
			h.logger.Error("Failed to stop process", "error", err)
			http.Error(w, fmt.Sprintf("Failed to stop process: %v", err), http.StatusInternalServerError)
			return
		}
	}

	// Call system reset method
	if resetter, ok := h.system.(interface{ ResetState() error }); ok {
		if err := resetter.ResetState(); err != nil {
			h.logger.Error("Failed to reset state", "error", err)
			http.Error(w, fmt.Sprintf("Failed to reset state: %v", err), http.StatusInternalServerError)
			return
		}
		h.logger.Info("State reset completed successfully")
		w.WriteHeader(http.StatusOK)
		fmt.Fprintln(w, "State reset completed successfully")
	} else {
		http.Error(w, "Reset state not supported", http.StatusNotImplemented)
	}
}
