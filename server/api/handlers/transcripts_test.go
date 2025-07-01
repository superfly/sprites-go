package handlers

import (
	"context"
	"encoding/json"
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"testing"

	"github.com/sprite-env/lib/api"
)

// mockSystemManagerWithTranscripts extends the mock to include transcript methods
type mockSystemManagerWithTranscripts struct {
	*mockSystemManager
	transcriptsEnabled bool
}

func newMockSystemManagerWithTranscripts() *mockSystemManagerWithTranscripts {
	return &mockSystemManagerWithTranscripts{
		mockSystemManager:  newMockSystemManager(),
		transcriptsEnabled: false, // Default to off as per requirements
	}
}

func (m *mockSystemManagerWithTranscripts) EnableTranscripts(ctx context.Context) error {
	m.transcriptsEnabled = true
	return nil
}

func (m *mockSystemManagerWithTranscripts) DisableTranscripts(ctx context.Context) error {
	m.transcriptsEnabled = false
	return nil
}

func (m *mockSystemManagerWithTranscripts) IsTranscriptsEnabled() bool {
	return m.transcriptsEnabled
}

func TestHandleTranscriptsEnable(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := newMockSystemManagerWithTranscripts()
	h := NewHandlers(logger, mockSys, config)

	tests := []struct {
		name            string
		method          string
		expectedStatus  int
		expectedEnabled bool
	}{
		{
			name:            "POST method enables transcripts",
			method:          http.MethodPost,
			expectedStatus:  http.StatusOK,
			expectedEnabled: true,
		},
		{
			name:            "GET method not allowed",
			method:          http.MethodGet,
			expectedStatus:  http.StatusMethodNotAllowed,
			expectedEnabled: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Reset state
			mockSys.transcriptsEnabled = false

			req := httptest.NewRequest(tt.method, "/transcripts/enable", nil)
			w := httptest.NewRecorder()

			h.HandleTranscriptsEnable(w, req)

			if w.Code != tt.expectedStatus {
				t.Errorf("Expected status %d, got %d", tt.expectedStatus, w.Code)
			}

			if tt.expectedStatus == http.StatusOK {
				// Check response body
				var response api.TranscriptsResponse
				if err := json.Unmarshal(w.Body.Bytes(), &response); err != nil {
					t.Fatalf("Failed to unmarshal response: %v", err)
				}

				if response.Enabled != tt.expectedEnabled {
					t.Errorf("Expected enabled=%v, got %v", tt.expectedEnabled, response.Enabled)
				}

				// Check that the system state was actually changed
				if mockSys.IsTranscriptsEnabled() != tt.expectedEnabled {
					t.Errorf("Expected system transcripts enabled=%v, got %v", tt.expectedEnabled, mockSys.IsTranscriptsEnabled())
				}
			}
		})
	}
}

func TestHandleTranscriptsDisable(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	config := Config{}
	mockSys := newMockSystemManagerWithTranscripts()
	h := NewHandlers(logger, mockSys, config)

	tests := []struct {
		name            string
		method          string
		expectedStatus  int
		expectedEnabled bool
	}{
		{
			name:            "POST method disables transcripts",
			method:          http.MethodPost,
			expectedStatus:  http.StatusOK,
			expectedEnabled: false,
		},
		{
			name:            "GET method not allowed",
			method:          http.MethodGet,
			expectedStatus:  http.StatusMethodNotAllowed,
			expectedEnabled: true, // State shouldn't change on error
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Start with transcripts enabled
			mockSys.transcriptsEnabled = true

			req := httptest.NewRequest(tt.method, "/transcripts/disable", nil)
			w := httptest.NewRecorder()

			h.HandleTranscriptsDisable(w, req)

			if w.Code != tt.expectedStatus {
				t.Errorf("Expected status %d, got %d", tt.expectedStatus, w.Code)
			}

			if tt.expectedStatus == http.StatusOK {
				// Check response body
				var response api.TranscriptsResponse
				if err := json.Unmarshal(w.Body.Bytes(), &response); err != nil {
					t.Fatalf("Failed to unmarshal response: %v", err)
				}

				if response.Enabled != tt.expectedEnabled {
					t.Errorf("Expected enabled=%v, got %v", tt.expectedEnabled, response.Enabled)
				}

				// Check that the system state was actually changed
				if mockSys.IsTranscriptsEnabled() != tt.expectedEnabled {
					t.Errorf("Expected system transcripts enabled=%v, got %v", tt.expectedEnabled, mockSys.IsTranscriptsEnabled())
				}
			} else {
				// On error, state should remain unchanged
				if mockSys.IsTranscriptsEnabled() != tt.expectedEnabled {
					t.Errorf("Expected system transcripts enabled=%v after error, got %v", tt.expectedEnabled, mockSys.IsTranscriptsEnabled())
				}
			}
		})
	}
}
