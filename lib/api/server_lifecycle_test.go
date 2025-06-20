package api

// Tests temporarily disabled - API lifecycle tests need rewrite for new architecture
// TODO: Rewrite tests to work with ProcessState and ComponentState

/*
import (
	"context"
	"fmt"
	"io"
	"log/slog"
	"net"
	"net/http"
	"os"
	"testing"
	"time"

	"lib"
)

func TestServerShutdown(t *testing.T) {
	// Save and restore env var
	oldToken := os.Getenv("SPRITE_HTTP_API_TOKEN")
	defer os.Setenv("SPRITE_HTTP_API_TOKEN", oldToken)
	os.Setenv("SPRITE_HTTP_API_TOKEN", "testtoken")

	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	mockState := &mockSystemState{}

	t.Run("graceful shutdown with in-flight request", func(t *testing.T) {
		// Create a test config
		config := &lib.ApplicationConfig{
			Exec: lib.ExecConfig{
				WrapperCommand:    []string{},
				TTYWrapperCommand: []string{},
			},
		}
		server := NewServer(":0", mockState, logger, config) // Use :0 for random port

		// Start the server
		if err := server.Start(); err != nil {
			t.Fatalf("failed to start server: %v", err)
		}

		// Wait a bit for server to start listening
		time.Sleep(100 * time.Millisecond)

		// The server's actual address is not directly accessible, so we need to try connecting
		// Since the Start() method launches the server in a goroutine, we need to find the actual port
		// For this test, let's use a fixed port instead
		server = NewServer(":18090", mockState, logger, config)
		if err := server.Start(); err != nil {
			t.Fatalf("failed to start server: %v", err)
		}
		time.Sleep(100 * time.Millisecond)

		// Create a slow handler that we'll use to test graceful shutdown
		slowHandler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			// Signal that request has started
			select {
			case <-r.Context().Done():
				// Context cancelled, return error
				http.Error(w, "request cancelled", http.StatusServiceUnavailable)
				return
			case <-time.After(200 * time.Millisecond):
				// Normal completion
				w.WriteHeader(http.StatusOK)
				w.Write([]byte("completed"))
			}
		})

		// Replace the exec handler with our slow handler for testing
		mux := http.NewServeMux()
		mux.Handle("/test", server.authMiddleware(slowHandler))
		server.server.Handler = mux

		// Start a request in a goroutine
		requestDone := make(chan struct{})
		requestErr := make(chan error, 1)

		go func() {
			req, err := http.NewRequest("GET", "http://localhost:18090/test", nil)
			if err != nil {
				requestErr <- err
				return
			}
			req.Header.Set("fly-replay-src", "state=api:testtoken")

			resp, err := http.DefaultClient.Do(req)
			if err != nil {
				requestErr <- err
				return
			}
			defer resp.Body.Close()

			body, _ := io.ReadAll(resp.Body)
			if resp.StatusCode != http.StatusOK {
				requestErr <- fmt.Errorf("unexpected status: %d, body: %s", resp.StatusCode, body)
				return
			}

			if string(body) != "completed" {
				requestErr <- fmt.Errorf("unexpected body: %s", body)
				return
			}

			close(requestDone)
		}()

		// Give the request time to start
		time.Sleep(50 * time.Millisecond)

		// Now stop the server with a timeout longer than the request
		stopCtx, cancel := context.WithTimeout(context.Background(), 1*time.Second)
		defer cancel()

		stopErr := server.Stop(stopCtx)
		if stopErr != nil {
			t.Errorf("server stop failed: %v", stopErr)
		}

		// Check if the request completed successfully
		select {
		case err := <-requestErr:
			t.Errorf("request failed: %v", err)
		case <-requestDone:
			// Request completed successfully
		case <-time.After(2 * time.Second):
			t.Error("request did not complete in time")
		}
	})

	t.Run("shutdown timeout with slow request", func(t *testing.T) {
		// Create a test config
		config := &lib.ApplicationConfig{
			Exec: lib.ExecConfig{
				WrapperCommand:    []string{},
				TTYWrapperCommand: []string{},
			},
		}
		server := NewServer(":18091", mockState, logger, config)

		// Start the server
		if err := server.Start(); err != nil {
			t.Fatalf("failed to start server: %v", err)
		}

		// Wait for server to start
		time.Sleep(100 * time.Millisecond)

		// Create a very slow handler
		verySlowHandler := http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
			// This will take longer than our shutdown timeout
			select {
			case <-r.Context().Done():
				// Context cancelled
				return
			case <-time.After(5 * time.Second):
				// Should not reach here
				w.WriteHeader(http.StatusOK)
			}
		})

		// Replace handler
		mux := http.NewServeMux()
		mux.Handle("/test", server.authMiddleware(verySlowHandler))
		server.server.Handler = mux

		// Start a request
		go func() {
			req, err := http.NewRequest("GET", "http://localhost:18091/test", nil)
			if err != nil {
				return
			}
			req.Header.Set("fly-replay-src", "state=api:testtoken")
			http.DefaultClient.Do(req)
		}()

		// Give request time to start
		time.Sleep(50 * time.Millisecond)

		// Stop with short timeout
		stopCtx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
		defer cancel()

		stopErr := server.Stop(stopCtx)
		if stopErr == nil {
			// This is actually fine - the server can forcibly close connections
			// The important thing is that Stop() returns
		}
	})

	t.Run("server refuses new connections after Stop", func(t *testing.T) {
		// Create a test config
		config := &lib.ApplicationConfig{
			Exec: lib.ExecConfig{
				WrapperCommand:    []string{},
				TTYWrapperCommand: []string{},
			},
		}
		server := NewServer(":18092", mockState, logger, config)

		// Start the server
		if err := server.Start(); err != nil {
			t.Fatalf("failed to start server: %v", err)
		}

		// Wait for server to start
		time.Sleep(100 * time.Millisecond)

		// Stop the server
		stopCtx, cancel := context.WithTimeout(context.Background(), 1*time.Second)
		defer cancel()

		if err := server.Stop(stopCtx); err != nil {
			t.Fatalf("failed to stop server: %v", err)
		}

		// Try to make a request - should fail
		req, err := http.NewRequest("GET", "http://localhost:18092/test", nil)
		if err != nil {
			t.Fatal(err)
		}
		req.Header.Set("fly-replay-src", "state=api:testtoken")

		// The request should fail (connection refused or similar)
		resp, err := http.DefaultClient.Do(req)
		if err == nil {
			resp.Body.Close()
			t.Error("expected request to fail after server stop, but it succeeded")
		}
	})
}
*/
