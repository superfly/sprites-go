package api

import (
	"context"
	"io"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"net/url"
	"strings"
	"testing"
	"time"

	sprites "github.com/superfly/sprites-go"
)

func newControlAPIServer(t *testing.T, h *Handlers) *httptest.Server {
	t.Helper()
	mux := http.NewServeMux()
	mux.HandleFunc("/v1/sprites/", func(w http.ResponseWriter, r *http.Request) {
		parts := strings.Split(strings.Trim(r.URL.Path, "/"), "/")
		if len(parts) == 4 && parts[0] == "v1" && parts[1] == "sprites" && parts[3] == "control" {
			h.HandleControl(w, r)
			return
		}
		if len(parts) == 3 && parts[0] == "v1" && parts[1] == "sprites" && parts[2] == "exec" {
			h.ExecHandler(w, r)
			return
		}
		http.NotFound(w, r)
	})
	return httptest.NewServer(mux)
}

func TestControlSDK_ExecEcho(t *testing.T) {
	h := &Handlers{logger: testLogger(t), system: &mockSystemManager{isRunning: true}}
	ts := newControlAPIServer(t, h)
	defer ts.Close()

	// Build base URL for SDK
	u, _ := url.Parse(ts.URL)
	u.Path = "/" // base
	client := sprites.NewClient(u.String(), "test-token")
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	sp := client.Sprite("foo")

	// Run an exec echo via SDK; SDK should use control connection when available
	cmd := sp.CommandContext(ctx, "echo", "hello")
	stdout := &strings.Builder{}
	cmd.Stdout = stdout
	if err := cmd.Run(); err != nil {
		t.Fatalf("exec via sdk failed: %v", err)
	}
	if strings.TrimSpace(stdout.String()) != "hello" {
		t.Fatalf("unexpected stdout: %q", stdout.String())
	}
}

func TestControlSDK_ExecStdin(t *testing.T) {
	h := &Handlers{logger: slog.New(slog.NewTextHandler(io.Discard, nil)), system: &mockSystemManager{isRunning: true}}
	ts := newControlAPIServer(t, h)
	defer ts.Close()

	u, _ := url.Parse(ts.URL)
	u.Path = "/"
	client := sprites.NewClient(u.String(), "test-token")
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	sp := client.Sprite("foo")

	// Read exactly 4 bytes from stdin using head -c 4
	cmd := sp.CommandContext(ctx, "sh", "-c", "head -c 4")
	cmd.Stdin = strings.NewReader("ABCD")
	stdout := &strings.Builder{}
	cmd.Stdout = stdout
	if err := cmd.Run(); err != nil {
		t.Fatalf("exec via sdk failed: %v", err)
	}
	if !strings.Contains(stdout.String(), "ABCD") {
		t.Fatalf("expected stdout to contain input bytes, got %q", stdout.String())
	}
}

func TestControlSDK_FallbackToExecOn404(t *testing.T) {
	h := &Handlers{logger: slog.New(slog.NewTextHandler(io.Discard, nil)), system: &mockSystemManager{isRunning: true}}
	mux := http.NewServeMux()
	// control path returns 404 explicitly
	mux.HandleFunc("/v1/sprites/", func(w http.ResponseWriter, r *http.Request) {
		parts := strings.Split(strings.Trim(r.URL.Path, "/"), "/")
		if len(parts) == 4 && parts[0] == "v1" && parts[1] == "sprites" && parts[3] == "control" {
			http.NotFound(w, r)
			return
		}
		if len(parts) == 4 && parts[0] == "v1" && parts[1] == "sprites" && parts[3] == "exec" {
			h.ExecHandler(w, r)
			return
		}
		http.NotFound(w, r)
	})
	ts := httptest.NewServer(mux)
	defer ts.Close()

	u, _ := url.Parse(ts.URL)
	u.Path = "/" // base
	client := sprites.NewClient(u.String(), "test-token")
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	sp := client.Sprite("foo")

	// Run an exec echo via SDK; should fall back to /exec successfully
	cmd := sp.CommandContext(ctx, "echo", "hello-fallback")
	stdout := &strings.Builder{}
	cmd.Stdout = stdout
	if err := cmd.Run(); err != nil {
		t.Fatalf("fallback exec via sdk failed: %v", err)
	}
	if strings.TrimSpace(stdout.String()) != "hello-fallback" {
		t.Fatalf("unexpected stdout: %q", stdout.String())
	}
}

func TestControlSDK_ExecTTY_Exits(t *testing.T) {
	h := &Handlers{logger: slog.New(slog.NewTextHandler(io.Discard, nil)), system: &mockSystemManager{isRunning: true}}
	ts := newControlAPIServer(t, h)
	defer ts.Close()

	u, _ := url.Parse(ts.URL)
	u.Path = "/"
	client := sprites.NewClient(u.String(), "test-token")
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	sp := client.Sprite("foo")

	cmd := sp.CommandContext(ctx, "sh", "-lc", "echo ttyok")
	cmd.SetTTY(true)
	_ = cmd.SetTTYSize(24, 80)

	// Ensure stdin is closed so the PTY input goroutine terminates
	if stdin, err := cmd.StdinPipe(); err == nil {
		_ = stdin.Close()
	}

	stdout := &strings.Builder{}
	cmd.Stdout = stdout
	if err := cmd.Run(); err != nil {
		t.Fatalf("tty exec via sdk failed: %v", err)
	}
	if strings.TrimSpace(stdout.String()) != "ttyok" {
		t.Fatalf("unexpected stdout: %q", stdout.String())
	}
}
