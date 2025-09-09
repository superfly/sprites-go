package api

import (
	"context"
	"encoding/json"
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"

	"github.com/superfly/sprite-env/pkg/tap"
)

// TestDebugCreateZombie tests the debug zombie creation endpoint
func TestDebugCreateZombie(t *testing.T) {
	// Create test dependencies
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	mockSys := newMockSystemManager()

	config := Config{
		APIToken: "test-token",
	}

	// Create server
	server, err := NewServer(config, mockSys, ctx)
	if err != nil {
		t.Fatalf("Failed to create server: %v", err)
	}

	// Set up test server
	mux := http.NewServeMux()
	server.setupEndpoints(mux)
	ts := httptest.NewServer(mux)
	defer ts.Close()

	// Create test request
	req, _ := http.NewRequest("POST", ts.URL+"/debug/create-zombie", strings.NewReader("{}"))
	req.Header.Set("Authorization", "Bearer test-token")
	req.Header.Set("Content-Type", "application/json")

	// Make request
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		t.Fatalf("Failed to make request: %v", err)
	}
	defer resp.Body.Close()

	// Check response
	if resp.StatusCode != http.StatusOK {
		t.Errorf("Expected status %d, got %d", http.StatusOK, resp.StatusCode)
	}

	// Parse response
	var result map[string]interface{}
	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		t.Fatalf("Failed to decode response: %v", err)
	}

	// Check response fields
	if _, ok := result["message"]; !ok {
		t.Error("Response missing 'message' field")
	}
	if _, ok := result["pid"]; !ok {
		t.Error("Response missing 'pid' field")
	}
	if _, ok := result["note"]; !ok {
		t.Error("Response missing 'note' field")
	}
}

// TestDebugCheckProcess tests the debug process check endpoint
func TestDebugCheckProcess(t *testing.T) {
	// Create test dependencies
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	mockSys := newMockSystemManager()

	config := Config{
		APIToken: "test-token",
	}

	// Create server
	server, err := NewServer(config, mockSys, ctx)
	if err != nil {
		t.Fatalf("Failed to create server: %v", err)
	}

	// Set up test server
	mux := http.NewServeMux()
	server.setupEndpoints(mux)
	ts := httptest.NewServer(mux)
	defer ts.Close()

	// Test cases
	tests := []struct {
		name           string
		method         string
		url            string
		expectedStatus int
	}{
		{
			name:           "Valid request",
			method:         "GET",
			url:            "/debug/check-process?pid=1",
			expectedStatus: http.StatusOK,
		},
		{
			name:           "Missing PID",
			method:         "GET",
			url:            "/debug/check-process",
			expectedStatus: http.StatusBadRequest,
		},
		{
			name:           "Invalid PID",
			method:         "GET",
			url:            "/debug/check-process?pid=invalid",
			expectedStatus: http.StatusBadRequest,
		},
		{
			name:           "Wrong method",
			method:         "POST",
			url:            "/debug/check-process?pid=1",
			expectedStatus: http.StatusMethodNotAllowed,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Create test request
			req, _ := http.NewRequest(tt.method, ts.URL+tt.url, nil)
			req.Header.Set("Authorization", "Bearer test-token")

			// Make request
			resp, err := http.DefaultClient.Do(req)
			if err != nil {
				t.Fatalf("Failed to make request: %v", err)
			}
			defer resp.Body.Close()

			// Check response status
			if resp.StatusCode != tt.expectedStatus {
				t.Errorf("Expected status %d, got %d", tt.expectedStatus, resp.StatusCode)
			}

			// For successful requests, check response format
			if resp.StatusCode == http.StatusOK {
				var result map[string]interface{}
				if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
					t.Fatalf("Failed to decode response: %v", err)
				}

				// Check required fields
				requiredFields := []string{"pid", "exists", "is_zombie"}
				for _, field := range requiredFields {
					if _, ok := result[field]; !ok {
						t.Errorf("Response missing required field: %s", field)
					}
				}
			}
		})
	}
}
