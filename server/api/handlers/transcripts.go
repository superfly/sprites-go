package handlers

import (
	"encoding/json"
	"net/http"

	"github.com/sprite-env/lib/api"
)

// HandleTranscriptsEnable enables transcript recording for future exec calls
func (h *Handlers) HandleTranscriptsEnable(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	if err := h.system.EnableTranscripts(r.Context()); err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(api.TranscriptsResponse{Enabled: true})
}

// HandleTranscriptsDisable disables transcript recording for future exec calls
func (h *Handlers) HandleTranscriptsDisable(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	if err := h.system.DisableTranscripts(r.Context()); err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(api.TranscriptsResponse{Enabled: false})
}
