package handlers

import (
	"context"
	"log/slog"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	gorillaws "github.com/gorilla/websocket"
	"github.com/superfly/sprite-env/pkg/terminal"
)

func TestHandleExecWithEnvAndWrapper(t *testing.T) {
	// Create a wrapper script that echoes environment variables
	wrapperScript := `#!/bin/sh
echo "WRAPPER_PID:$$"
echo "WRAPPER_ENV_TEST_VAR:$TEST_VAR"
echo "WRAPPER_ENV_CUSTOM_VAR:$CUSTOM_VAR"
echo "WRAPPER_ENV_PATH:$PATH"
exec "$@"
`

	// Create the wrapper script file
	tmpFile := filepath.Join(t.TempDir(), "test-wrapper.sh")
	if err := os.WriteFile(tmpFile, []byte(wrapperScript), 0755); err != nil {
		t.Fatalf("failed to create wrapper script: %v", err)
	}

	// Create handlers with the wrapper command
	h := &Handlers{
		logger:             slog.New(slog.NewTextHandler(os.Stdout, nil)),
		system:             &mockSystemManager{},
		execWrapperCommand: []string{tmpFile},
	}

	// Set up test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		h.HandleExec(w, r)
	}))
	defer server.Close()

	// Test URL with environment variables
	wsURL := "ws" + strings.TrimPrefix(server.URL, "http") +
		"/exec?cmd=env&env=TEST_VAR=wrapper_test_value&env=CUSTOM_VAR=hello_world&env=PATH=/custom/path"

	// Connect as a client
	dialer := gorillaws.DefaultDialer
	conn, _, err := dialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("failed to connect: %v", err)
	}
	defer conn.Close()

	// Collect output
	var output strings.Builder
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	// Read messages until we get the exit code
	go func() {
		for {
			select {
			case <-ctx.Done():
				return
			default:
				messageType, data, err := conn.ReadMessage()
				if err != nil {
					return
				}

				if messageType == gorillaws.BinaryMessage && len(data) > 1 {
					streamID := terminal.StreamID(data[0])
					if streamID == terminal.StreamStdout {
						output.Write(data[1:])
					} else if streamID == terminal.StreamExit {
						// Got exit code, we're done
						return
					}
				}
			}
		}
	}()

	// Wait for completion or timeout
	<-ctx.Done()

	outputStr := output.String()

	// Verify wrapper was called
	if !strings.Contains(outputStr, "WRAPPER_PID:") {
		t.Errorf("Expected wrapper to be called, output: %s", outputStr)
	}

	// Verify environment variables were passed to wrapper
	if !strings.Contains(outputStr, "WRAPPER_ENV_TEST_VAR:wrapper_test_value") {
		t.Errorf("Expected TEST_VAR to be passed to wrapper, output: %s", outputStr)
	}

	if !strings.Contains(outputStr, "WRAPPER_ENV_CUSTOM_VAR:hello_world") {
		t.Errorf("Expected CUSTOM_VAR to be passed to wrapper, output: %s", outputStr)
	}

	// Verify PATH was passed to wrapper
	if !strings.Contains(outputStr, "WRAPPER_ENV_PATH:/custom/path") {
		t.Errorf("Expected PATH to be passed to wrapper, output: %s", outputStr)
	}

	// The wrapper should have executed the env command, but we're mainly testing
	// that environment variables are passed to the wrapper correctly
	// The wrapper output shows the environment variables are available
	t.Logf("Wrapper output: %s", outputStr)
}

func TestHandleExecWithEnvWithoutWrapper(t *testing.T) {
	// Test without wrapper to ensure env vars work in both cases
	h := &Handlers{
		logger: slog.New(slog.NewTextHandler(os.Stdout, nil)),
		system: &mockSystemManager{},
	}

	// Set up test server
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		h.HandleExec(w, r)
	}))
	defer server.Close()

	// Test URL with environment variables
	wsURL := "ws" + strings.TrimPrefix(server.URL, "http") +
		"/exec?cmd=env&env=TEST_VAR=direct_test_value&env=CUSTOM_VAR=direct_hello"

	// Connect as a client
	dialer := gorillaws.DefaultDialer
	conn, _, err := dialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("failed to connect: %v", err)
	}
	defer conn.Close()

	// Collect output
	var output strings.Builder
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	// Read messages until we get the exit code
	go func() {
		for {
			select {
			case <-ctx.Done():
				return
			default:
				messageType, data, err := conn.ReadMessage()
				if err != nil {
					return
				}

				if messageType == gorillaws.BinaryMessage && len(data) > 1 {
					streamID := terminal.StreamID(data[0])
					if streamID == terminal.StreamStdout {
						output.Write(data[1:])
					} else if streamID == terminal.StreamExit {
						// Got exit code, we're done
						return
					}
				}
			}
		}
	}()

	// Wait for completion or timeout
	<-ctx.Done()

	outputStr := output.String()

	// Verify environment variables were passed directly to command
	if !strings.Contains(outputStr, "TEST_VAR=direct_test_value") {
		t.Errorf("Expected TEST_VAR to be passed to command, output: %s", outputStr)
	}

	if !strings.Contains(outputStr, "CUSTOM_VAR=direct_hello") {
		t.Errorf("Expected CUSTOM_VAR to be passed to command, output: %s", outputStr)
	}
}
