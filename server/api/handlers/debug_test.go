package handlers

import (
	"encoding/json"
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"testing"
)

// TestHandleDebugCreateZombie tests the debug zombie creation handler
func TestHandleDebugCreateZombie(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	commandCh := make(chan Command, 1)
	config := Config{}
	mockPM := &mockProcessManager{}
	h := NewHandlers(logger, commandCh, config, mockPM)

	tests := []struct {
		name           string
		method         string
		expectedStatus int
	}{
		{
			name:           "POST method creates zombie",
			method:         http.MethodPost,
			expectedStatus: http.StatusOK,
		},
		{
			name:           "GET method not allowed",
			method:         http.MethodGet,
			expectedStatus: http.StatusMethodNotAllowed,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			req := httptest.NewRequest(tt.method, "/debug/create-zombie", nil)
			rr := httptest.NewRecorder()

			h.HandleDebugCreateZombie(rr, req)

			if rr.Code != tt.expectedStatus {
				t.Errorf("expected status %d, got %d", tt.expectedStatus, rr.Code)
			}

			// For successful requests, verify response format
			if tt.expectedStatus == http.StatusOK {
				var result map[string]interface{}
				if err := json.NewDecoder(rr.Body).Decode(&result); err != nil {
					t.Fatalf("Failed to decode response: %v", err)
				}

				// Check required fields
				requiredFields := []string{"message", "pid", "note"}
				for _, field := range requiredFields {
					if _, ok := result[field]; !ok {
						t.Errorf("Response missing required field: %s", field)
					}
				}
			}
		})
	}
}

// TestHandleDebugCheckProcess tests the debug process check handler
func TestHandleDebugCheckProcess(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	commandCh := make(chan Command, 1)
	config := Config{}
	mockPM := &mockProcessManager{}
	h := NewHandlers(logger, commandCh, config, mockPM)

	tests := []struct {
		name           string
		method         string
		queryParams    string
		expectedStatus int
	}{
		{
			name:           "Valid PID",
			method:         http.MethodGet,
			queryParams:    "?pid=1",
			expectedStatus: http.StatusOK,
		},
		{
			name:           "Missing PID",
			method:         http.MethodGet,
			queryParams:    "",
			expectedStatus: http.StatusBadRequest,
		},
		{
			name:           "Invalid PID format",
			method:         http.MethodGet,
			queryParams:    "?pid=invalid",
			expectedStatus: http.StatusBadRequest,
		},
		{
			name:           "POST method not allowed",
			method:         http.MethodPost,
			queryParams:    "?pid=1",
			expectedStatus: http.StatusMethodNotAllowed,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			req := httptest.NewRequest(tt.method, "/debug/check-process"+tt.queryParams, nil)
			rr := httptest.NewRecorder()

			h.HandleDebugCheckProcess(rr, req)

			if rr.Code != tt.expectedStatus {
				t.Errorf("expected status %d, got %d", tt.expectedStatus, rr.Code)
			}

			// For successful requests, verify response format
			if tt.expectedStatus == http.StatusOK {
				var result map[string]interface{}
				if err := json.NewDecoder(rr.Body).Decode(&result); err != nil {
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
