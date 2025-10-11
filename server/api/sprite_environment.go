package api

import (
	"encoding/json"
	"fmt"
	"net/http"

	"github.com/superfly/sprite-env/pkg/tap"
)

// SetSpriteEnvironmentRequest represents the request body for setting sprite environment
type SetSpriteEnvironmentRequest struct {
	SpriteName string `json:"sprite_name"`
	SpriteURL  string `json:"sprite_url"`
	OrgID      string `json:"org_id"`
	SpriteID   string `json:"sprite_id"`
}

// HandleSetSpriteEnvironment handles POST /v1/sprites/:name/environment
func (h *Handlers) HandleSetSpriteEnvironment(w http.ResponseWriter, r *http.Request) {
	ctx := r.Context()
	logger := tap.Logger(ctx)

	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	var req SetSpriteEnvironmentRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		logger.Error("Failed to decode sprite environment request", "error", err)
		http.Error(w, fmt.Sprintf("Invalid request body: %v", err), http.StatusBadRequest)
		return
	}

	// Validate required fields
	if req.SpriteName == "" {
		http.Error(w, "sprite_name is required", http.StatusBadRequest)
		return
	}
	if req.SpriteURL == "" {
		http.Error(w, "sprite_url is required", http.StatusBadRequest)
		return
	}
	if req.OrgID == "" {
		http.Error(w, "org_id is required", http.StatusBadRequest)
		return
	}
	if req.SpriteID == "" {
		http.Error(w, "sprite_id is required", http.StatusBadRequest)
		return
	}

	// Call system method
	response, err := h.system.SetSpriteEnvironment(ctx, &req)
	if err != nil {
		logger.Error("Failed to set sprite environment", "error", err)
		// Check for specific error types
		if err.Error() == "sprite name and org cannot be changed once set" {
			http.Error(w, err.Error(), http.StatusConflict)
			return
		}
		http.Error(w, fmt.Sprintf("Failed to set sprite environment: %v", err), http.StatusInternalServerError)
		return
	}

	// Return response as JSON
	w.Header().Set("Content-Type", "application/json")
	if err := json.NewEncoder(w).Encode(response); err != nil {
		logger.Error("Failed to encode response", "error", err)
	}
}
