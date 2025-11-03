package api

import (
	"context"
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"testing"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

func setupHandlersForTest(t *testing.T) *Handlers {
	t.Helper()
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	ctx := context.Background()
	ctx = tap.WithLogger(ctx, logger)
	config := HandlerConfig{MaxWaitTime: 30 * time.Second}
	mockSys := newMockSystemManager()
	return NewHandlers(ctx, mockSys, config)
}

func TestHandleDeleteCheckpoint_Method(t *testing.T) {
	h := setupHandlersForTest(t)
	rr := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodGet, "/checkpoints/v1", nil)
	h.HandleDeleteCheckpoint(rr, req)
	if rr.Code != http.StatusMethodNotAllowed {
		t.Fatalf("expected %d, got %d", http.StatusMethodNotAllowed, rr.Code)
	}
}

func TestHandleDeleteCheckpoint_Success(t *testing.T) {
	h := setupHandlersForTest(t)
	rr := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodDelete, "/checkpoints/v1", nil)
	h.HandleDeleteCheckpoint(rr, req)
	if rr.Code != http.StatusNoContent {
		t.Fatalf("expected %d, got %d", http.StatusNoContent, rr.Code)
	}

	// After delete, list should not include v1 anymore (mock enforces state)
	rr2 := httptest.NewRecorder()
	req2 := httptest.NewRequest(http.MethodGet, "/checkpoints", nil)
	h.HandleListCheckpoints(rr2, req2)
	if rr2.Code != http.StatusOK {
		t.Fatalf("expected %d, got %d", http.StatusOK, rr2.Code)
	}
}

func TestHandleDeleteCheckpoint_ConflictOnActive(t *testing.T) {
	h := setupHandlersForTest(t)
	rr := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodDelete, "/checkpoints/active", nil)
	h.HandleDeleteCheckpoint(rr, req)
	if rr.Code != http.StatusConflict {
		t.Fatalf("expected %d, got %d", http.StatusConflict, rr.Code)
	}
}

func TestHandleDeleteCheckpoint_NotFound(t *testing.T) {
	h := setupHandlersForTest(t)
	rr := httptest.NewRecorder()
	req := httptest.NewRequest(http.MethodDelete, "/checkpoints/v999", nil)
	h.HandleDeleteCheckpoint(rr, req)
	if rr.Code != http.StatusNotFound {
		t.Fatalf("expected %d, got %d", http.StatusNotFound, rr.Code)
	}
}
