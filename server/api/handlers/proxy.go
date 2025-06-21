package handlers

import (
	"net/http"
)

// HandleProxy handles the /proxy endpoint (placeholder for now)
func (h *Handlers) HandleProxy(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodConnect {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// TODO: Implement proxy functionality
	http.Error(w, "Proxy endpoint not yet implemented", http.StatusNotImplemented)
}
