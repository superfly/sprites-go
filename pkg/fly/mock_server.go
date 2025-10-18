package fly

import (
	"encoding/json"
	"fmt"
	"net"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"sync"
)

// MockServer is a mock HTTP server that simulates the Fly local API
type MockServer struct {
	listener net.Listener
	server   *http.Server
	mux      *http.ServeMux
	socketPath string
	secrets  map[string]Secret
	mu       sync.RWMutex
	started  bool
}

// NewMockServer creates a new mock Fly API server
func NewMockServer() (*MockServer, error) {
	// Create a temporary socket path
	tmpDir := os.TempDir()
	socketPath := filepath.Join(tmpDir, fmt.Sprintf("fly-mock-%d.sock", os.Getpid()))

	// Remove any existing socket file
	os.Remove(socketPath)

	listener, err := net.Listen("unix", socketPath)
	if err != nil {
		return nil, fmt.Errorf("failed to create unix listener: %w", err)
	}

	mux := http.NewServeMux()
	m := &MockServer{
		listener:   listener,
		socketPath: socketPath,
		mux:        mux,
		secrets:    make(map[string]Secret),
	}

	// Register handlers
	mux.HandleFunc("/", m.handleRequest)

	m.server = &http.Server{Handler: mux}

	return m, nil
}

// Start starts the mock server
func (m *MockServer) Start() error {
	m.mu.Lock()
	if m.started {
		m.mu.Unlock()
		return fmt.Errorf("server already started")
	}
	m.started = true
	m.mu.Unlock()

	go m.server.Serve(m.listener)
	return nil
}

// Stop stops the mock server and cleans up the socket file
func (m *MockServer) Stop() error {
	if m.server != nil {
		m.server.Close()
	}
	if m.listener != nil {
		m.listener.Close()
	}
	if m.socketPath != "" {
		os.Remove(m.socketPath)
	}
	return nil
}

// SocketPath returns the path to the unix socket
func (m *MockServer) SocketPath() string {
	return m.socketPath
}

// SetSecret adds or updates a secret in the mock server
func (m *MockServer) SetSecret(secret Secret) {
	m.mu.Lock()
	defer m.mu.Unlock()
	m.secrets[secret.Name] = secret
}

// handleRequest routes requests to the appropriate handler
func (m *MockServer) handleRequest(w http.ResponseWriter, r *http.Request) {
	path := r.URL.Path
	method := r.Method

	// Parse the path
	parts := strings.Split(strings.Trim(path, "/"), "/")

	// Handle suspend: POST /v1/apps/{app}/machines/{machine}/suspend
	if method == http.MethodPost && len(parts) == 6 && parts[0] == "v1" && parts[1] == "apps" && parts[3] == "machines" && parts[5] == "suspend" {
		m.handleSuspend(w, r, parts[2], parts[4])
		return
	}

	// Handle list secrets: GET /v1/apps/{app}/secrets
	if method == http.MethodGet && len(parts) == 4 && parts[0] == "v1" && parts[1] == "apps" && parts[3] == "secrets" {
		m.handleListSecrets(w, r, parts[2])
		return
	}

	// Handle get secret: GET /v1/apps/{app}/secrets/{secret}
	if method == http.MethodGet && len(parts) == 5 && parts[0] == "v1" && parts[1] == "apps" && parts[3] == "secrets" {
		m.handleGetSecret(w, r, parts[2], parts[4])
		return
	}

	// Not found
	http.NotFound(w, r)
}

// handleSuspend handles machine suspend requests
func (m *MockServer) handleSuspend(w http.ResponseWriter, r *http.Request, app, machine string) {
	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	json.NewEncoder(w).Encode(map[string]string{
		"status": "suspended",
	})
}

// handleListSecrets handles secret list requests
func (m *MockServer) handleListSecrets(w http.ResponseWriter, r *http.Request, app string) {
	m.mu.RLock()
	defer m.mu.RUnlock()

	// Check query parameters
	minVersion := r.URL.Query().Get("min_version")
	showSecrets := r.URL.Query().Get("show_secrets")

	// Build response
	secrets := make([]Secret, 0, len(m.secrets))
	for _, secret := range m.secrets {
		s := secret
		// If show_secrets is not true, clear the value
		if showSecrets != "true" {
			s.Value = ""
		}
		secrets = append(secrets, s)
	}

	// Filter by min_version if provided (simplified - just check if digest matches)
	if minVersion != "" {
		filtered := make([]Secret, 0)
		for _, s := range secrets {
			if s.Digest >= minVersion {
				filtered = append(filtered, s)
			}
		}
		secrets = filtered
	}

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	json.NewEncoder(w).Encode(SecretsResponse{
		Secrets: secrets,
	})
}

// handleGetSecret handles get secret requests
func (m *MockServer) handleGetSecret(w http.ResponseWriter, r *http.Request, app, secretName string) {
	m.mu.RLock()
	defer m.mu.RUnlock()

	// Check query parameters
	showSecrets := r.URL.Query().Get("show_secrets")

	secret, exists := m.secrets[secretName]
	if !exists {
		w.Header().Set("Content-Type", "application/json")
		w.WriteHeader(http.StatusNotFound)
		json.NewEncoder(w).Encode(map[string]string{
			"error": "secret not found",
		})
		return
	}

	// If show_secrets is not true, clear the value
	if showSecrets != "true" {
		secret.Value = ""
	}

	w.Header().Set("Content-Type", "application/json")
	w.WriteHeader(http.StatusOK)
	json.NewEncoder(w).Encode(secret)
}
