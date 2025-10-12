package api

import (
	"encoding/json"
	"net/http"
	"strings"
	"time"

	"github.com/superfly/sprite-env/pkg/services"
)

// ServiceRequest represents the request body for creating/updating services
type ServiceRequest struct {
	Cmd   string   `json:"cmd"`
	Args  []string `json:"args"`
	Needs []string `json:"needs"`
}

// ServiceSignalRequest represents the request body for signaling services
type ServiceSignalRequest struct {
	Name   string `json:"name"`
	Signal string `json:"signal"`
}

// ServiceLogEvent represents a log event in NDJSON format for service operations
type ServiceLogEvent struct {
	Type      string            `json:"type"` // "stdout", "stderr", "exit", "error", "complete", "started"
	Data      string            `json:"data,omitempty"`
	ExitCode  *int              `json:"exit_code,omitempty"`
	Timestamp int64             `json:"timestamp"`
	LogFiles  map[string]string `json:"log_files,omitempty"` // For "complete" event
}

// HandleListServices handles GET /v1/services
func (h *Handlers) HandleListServices(w http.ResponseWriter, r *http.Request) {
	svcList, err := h.system.GetServicesManager().ListServices()
	if err != nil {
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}

	// Get states for all services
	type serviceWithState struct {
		*services.Service
		State *services.ServiceState `json:"state,omitempty"`
	}

	result := make([]serviceWithState, len(svcList))
	for i, svc := range svcList {
		state, _ := h.system.GetServicesManager().GetServiceState(svc.Name)
		result[i] = serviceWithState{
			Service: svc,
			State:   state,
		}
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(result)
}

// HandleGetService handles GET /v1/services/{name}
func (h *Handlers) HandleGetService(w http.ResponseWriter, r *http.Request) {
	name := r.PathValue("name")
	if name == "" {
		http.Error(w, "service name required", http.StatusBadRequest)
		return
	}

	svc, err := h.system.GetServicesManager().GetService(name)
	if err != nil {
		if strings.Contains(err.Error(), "not found") {
			http.Error(w, err.Error(), http.StatusNotFound)
		} else {
			http.Error(w, err.Error(), http.StatusInternalServerError)
		}
		return
	}

	state, _ := h.system.GetServicesManager().GetServiceState(name)

	result := struct {
		*services.Service
		State *services.ServiceState `json:"state,omitempty"`
	}{
		Service: svc,
		State:   state,
	}

	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(result)
}

// HandleCreateService handles PUT /v1/services/{name}
func (h *Handlers) HandleCreateService(w http.ResponseWriter, r *http.Request) {
	name := r.PathValue("name")
	if name == "" {
		http.Error(w, "service name required", http.StatusBadRequest)
		return
	}

	var req ServiceRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, "invalid request body", http.StatusBadRequest)
		return
	}

	// Validate required fields
	if req.Cmd == "" {
		http.Error(w, "cmd field is required", http.StatusBadRequest)
		return
	}

	// Parse monitoring duration from query parameter (default to 5 seconds)
	duration := 5 * time.Second
	if durationStr := r.URL.Query().Get("duration"); durationStr != "" {
		if d, err := time.ParseDuration(durationStr); err == nil && d > 0 {
			duration = d
		}
	}
	// Also support "timeout" for backwards compatibility
	if durationStr := r.URL.Query().Get("timeout"); durationStr != "" {
		if d, err := time.ParseDuration(durationStr); err == nil && d > 0 {
			duration = d
		}
	}

	svc := &services.Service{
		Name:  name,
		Cmd:   req.Cmd,
		Args:  req.Args,
		Needs: req.Needs,
	}

	// Create the service without starting it
	if err := h.system.GetServicesManager().CreateService(svc); err != nil {
		if strings.Contains(err.Error(), "dependency") || strings.Contains(err.Error(), "circular") {
			http.Error(w, err.Error(), http.StatusBadRequest)
		} else {
			http.Error(w, err.Error(), http.StatusInternalServerError)
		}
		return
	}

	// Set up streaming response headers
	w.Header().Set("Content-Type", "application/x-ndjson")
	w.Header().Set("Cache-Control", "no-cache")
	w.Header().Set("X-Content-Type-Options", "nosniff")
	w.WriteHeader(http.StatusOK)

	// Enable flushing
	flusher, ok := w.(http.Flusher)
	if !ok {
		// Fall back to non-streaming response
		event := ServiceLogEvent{
			Type:      "error",
			Data:      "streaming not supported",
			Timestamp: time.Now().UnixMilli(),
		}
		json.NewEncoder(w).Encode(event)
		return
	}

	// Get log directory from system config
	logDir := h.system.GetLogDir()

	// Start the service and stream logs for the duration
	streamServiceExecution(h.system.GetServicesManager(), logDir, w, name, duration, flusher, h.logger)
}

// HandleDeleteService handles DELETE /v1/services/{name}
func (h *Handlers) HandleDeleteService(w http.ResponseWriter, r *http.Request) {
	name := r.PathValue("name")
	if name == "" {
		http.Error(w, "service name required", http.StatusBadRequest)
		return
	}

	// Delete the service (which stops it)
	if err := h.system.GetServicesManager().DeleteService(name); err != nil {
		if strings.Contains(err.Error(), "not found") {
			http.Error(w, err.Error(), http.StatusNotFound)
		} else if strings.Contains(err.Error(), "running") || strings.Contains(err.Error(), "depends") {
			http.Error(w, err.Error(), http.StatusConflict)
		} else {
			http.Error(w, err.Error(), http.StatusInternalServerError)
		}
		return
	}

	// Wait for the service to stop (max 10 seconds)
	if err := h.system.GetServicesManager().WaitForStop(name, 10*time.Second); err != nil {
		h.logger.Warn("service did not stop within timeout", "name", name, "error", err)
		// Don't fail the request - the delete was successful
	}

	w.WriteHeader(http.StatusNoContent)
}

// HandleStartService handles POST /v1/services/{name}/start
func (h *Handlers) HandleStartService(w http.ResponseWriter, r *http.Request) {
	name := r.PathValue("name")
	if name == "" {
		http.Error(w, "service name required", http.StatusBadRequest)
		return
	}

	// Start the service
	if err := h.system.GetServicesManager().StartService(name); err != nil {
		if strings.Contains(err.Error(), "not found") {
			http.Error(w, err.Error(), http.StatusNotFound)
		} else if strings.Contains(err.Error(), "already") {
			http.Error(w, err.Error(), http.StatusConflict)
		} else {
			http.Error(w, err.Error(), http.StatusInternalServerError)
		}
		return
	}

	w.WriteHeader(http.StatusNoContent)
}

// HandleStopService handles POST /v1/services/{name}/stop
// Blocks until the service is fully stopped (with timeout)
func (h *Handlers) HandleStopService(w http.ResponseWriter, r *http.Request) {
	name := r.PathValue("name")
	if name == "" {
		http.Error(w, "service name required", http.StatusBadRequest)
		return
	}

	// Stop the service
	if err := h.system.GetServicesManager().StopService(name); err != nil {
		if strings.Contains(err.Error(), "not found") {
			http.Error(w, err.Error(), http.StatusNotFound)
		} else if strings.Contains(err.Error(), "not running") {
			http.Error(w, err.Error(), http.StatusConflict)
		} else if strings.Contains(err.Error(), "depends") {
			http.Error(w, err.Error(), http.StatusConflict)
		} else {
			http.Error(w, err.Error(), http.StatusInternalServerError)
		}
		return
	}

	// Wait for the service to stop (max 10 seconds)
	if err := h.system.GetServicesManager().WaitForStop(name, 10*time.Second); err != nil {
		h.logger.Error("service did not stop within timeout", "name", name, "error", err)
		http.Error(w, "service did not stop within timeout", http.StatusRequestTimeout)
		return
	}

	w.WriteHeader(http.StatusNoContent)
}

// HandleSignalService handles POST /v1/services/signal
func (h *Handlers) HandleSignalService(w http.ResponseWriter, r *http.Request) {
	var req ServiceSignalRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		http.Error(w, "invalid request body", http.StatusBadRequest)
		return
	}

	// Validate request
	if req.Name == "" {
		http.Error(w, "service name required", http.StatusBadRequest)
		return
	}
	if req.Signal == "" {
		http.Error(w, "signal required", http.StatusBadRequest)
		return
	}

	// Send the signal
	if err := h.system.GetServicesManager().SignalService(req.Name, req.Signal); err != nil {
		if strings.Contains(err.Error(), "not found") {
			http.Error(w, err.Error(), http.StatusNotFound)
		} else if strings.Contains(err.Error(), "not running") {
			http.Error(w, err.Error(), http.StatusConflict)
		} else if strings.Contains(err.Error(), "invalid signal") || strings.Contains(err.Error(), "unknown signal") {
			http.Error(w, err.Error(), http.StatusBadRequest)
		} else {
			http.Error(w, err.Error(), http.StatusInternalServerError)
		}
		return
	}

	// For TERM and KILL signals, wait for the process to stop
	if strings.ToUpper(req.Signal) == "TERM" || strings.ToUpper(req.Signal) == "SIGTERM" ||
		strings.ToUpper(req.Signal) == "KILL" || strings.ToUpper(req.Signal) == "SIGKILL" {
		// Wait for the service to stop (max 10 seconds)
		if err := h.system.GetServicesManager().WaitForStop(req.Name, 10*time.Second); err != nil {
			h.logger.Warn("service did not stop within timeout after signal", "name", req.Name, "signal", req.Signal, "error", err)
			// Don't fail the request - the signal was sent successfully
		}
	}

	w.WriteHeader(http.StatusNoContent)
}
