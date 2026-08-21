package sprites

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"io"
	"net/http"
	"net/http/httptest"
	"os"
	"strings"
	"syscall"
	"testing"
	"testing/iotest"
	"time"

	"github.com/gorilla/websocket"
)

type recordedStreamFrame struct {
	stream StreamID
	data   []byte
}

type recordingStreamSocket struct {
	frames []recordedStreamFrame
}

func (w *recordingStreamSocket) WriteStream(stream StreamID, data []byte) error {
	w.frames = append(w.frames, recordedStreamFrame{
		stream: stream,
		data:   bytes.Clone(data),
	})

	return nil
}

func TestCopyNonTTYStdinUsesStreamFrames(t *testing.T) {
	socket := &recordingStreamSocket{}

	n, err := copyNonTTYStdin(socket, strings.NewReader("hello\n"))
	if err != nil {
		t.Fatalf("copyNonTTYStdin() error = %v", err)
	}
	if n != 6 {
		t.Fatalf("copyNonTTYStdin() copied %d bytes, want 6", n)
	}
	if len(socket.frames) != 2 {
		t.Fatalf("got %d frames, want stdin and EOF frames", len(socket.frames))
	}
	if socket.frames[0].stream != StreamStdin || string(socket.frames[0].data) != "hello\n" {
		t.Errorf("stdin frame = %#v, want stream %d with payload %q", socket.frames[0], StreamStdin, "hello\n")
	}
	if socket.frames[1].stream != StreamStdinEOF || len(socket.frames[1].data) != 0 {
		t.Errorf("EOF frame = %#v, want empty stream %d frame", socket.frames[1], StreamStdinEOF)
	}
}

func TestCopyNonTTYStdinSendsEOFAfterReadError(t *testing.T) {
	socket := &recordingStreamSocket{}
	copyErr := errors.New("read failed")
	stdin := io.MultiReader(strings.NewReader("hello"), iotest.ErrReader(copyErr))

	n, err := copyNonTTYStdin(socket, stdin)
	if !errors.Is(err, copyErr) {
		t.Fatalf("copyNonTTYStdin() error = %v, want %v", err, copyErr)
	}
	if n != 5 {
		t.Fatalf("copyNonTTYStdin() copied %d bytes, want 5", n)
	}
	if len(socket.frames) != 2 {
		t.Fatalf("got %d frames, want stdin and EOF frames", len(socket.frames))
	}
	if socket.frames[0].stream != StreamStdin || string(socket.frames[0].data) != "hello" {
		t.Errorf("stdin frame = %#v, want stream %d with payload %q", socket.frames[0], StreamStdin, "hello")
	}
	if socket.frames[1].stream != StreamStdinEOF || len(socket.frames[1].data) != 0 {
		t.Errorf("EOF frame = %#v, want empty stream %d frame", socket.frames[1], StreamStdinEOF)
	}
}

func TestCmdWaitPreservesWebSocketReadError(t *testing.T) {
	const closeReason = "transport interrupted"

	serverErr := make(chan error, 1)
	server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		conn, err := (&websocket.Upgrader{}).Upgrade(w, r, nil)
		if err != nil {
			serverErr <- err
			return
		}
		defer conn.Close()

		serverErr <- conn.WriteControl(
			websocket.CloseMessage,
			websocket.FormatCloseMessage(websocket.CloseInternalServerErr, closeReason),
			time.Now().Add(time.Second),
		)
	}))
	defer server.Close()

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	req, err := http.NewRequestWithContext(ctx, http.MethodGet, "ws"+strings.TrimPrefix(server.URL, "http"), nil)
	if err != nil {
		t.Fatalf("NewRequestWithContext() error = %v", err)
	}

	stdinReader, stdinWriter := io.Pipe()
	defer stdinReader.Close()
	defer stdinWriter.Close()

	wsCmd := newWSCmdContext(ctx, req, "true")
	wsCmd.Stdin = stdinReader
	if err := wsCmd.Start(); err != nil {
		t.Fatalf("wsCmd.Start() error = %v", err)
	}

	cmd := &Cmd{started: true, wsCmd: wsCmd}
	err = cmd.Wait()
	_ = stdinWriter.Close()

	var closeErr *websocket.CloseError
	if !errors.As(err, &closeErr) {
		t.Fatalf("Cmd.Wait() error = %v (%T), want *websocket.CloseError", err, err)
	}
	if closeErr.Code != websocket.CloseInternalServerErr {
		t.Errorf("close code = %d, want %d", closeErr.Code, websocket.CloseInternalServerErr)
	}
	if closeErr.Text != closeReason {
		t.Errorf("close reason = %q, want %q", closeErr.Text, closeReason)
	}
	if err := <-serverErr; err != nil {
		t.Fatalf("server close error = %v", err)
	}
}

func TestCmdString(t *testing.T) {
	client := New("test-token", WithBaseURL("http://localhost:8080"))
	sprite := client.Sprite("my-sprite")

	cmd := sprite.Command("echo", "hello", "world")

	str := cmd.String()
	if str != "echo [hello world]" {
		t.Errorf("String() = %q, want %q", str, "echo [hello world]")
	}
}

func TestCmdBuildWebSocketURL(t *testing.T) {
	tests := []struct {
		name              string
		spriteName        string
		serverVersion     string
		useLegacyEndpoint bool
		cmd               *Cmd
		wantPath          string
		wantQuery         map[string][]string
	}{
		{
			name:       "basic command",
			spriteName: "my-sprite",
			cmd: &Cmd{
				Path: "echo",
				Args: []string{"echo", "hello"},
			},
			wantPath: "/v1/sprites/my-sprite/exec",
			wantQuery: map[string][]string{
				"cmd":  {"echo", "hello"},
				"path": {"echo"},
			},
		},
		{
			name:       "command with environment",
			spriteName: "test-sprite",
			cmd: &Cmd{
				Path: "env",
				Args: []string{"env"},
				Env:  []string{"FOO=bar", "BAZ=qux"},
			},
			wantPath: "/v1/sprites/test-sprite/exec",
			wantQuery: map[string][]string{
				"cmd":  {"env"},
				"path": {"env"},
				"env":  {"FOO=bar", "BAZ=qux"},
			},
		},
		{
			name:       "command with working dir",
			spriteName: "my-sprite",
			cmd: &Cmd{
				Path: "pwd",
				Args: []string{"pwd"},
				Dir:  "/tmp",
			},
			wantPath: "/v1/sprites/my-sprite/exec",
			wantQuery: map[string][]string{
				"cmd":  {"pwd"},
				"path": {"pwd"},
				"dir":  {"/tmp"},
			},
		},
		{
			name:       "command with TTY",
			spriteName: "my-sprite",
			cmd: &Cmd{
				Path:    "bash",
				Args:    []string{"bash"},
				tty:     true,
				ttySize: &ttySize{Rows: 24, Cols: 80},
			},
			wantPath: "/v1/sprites/my-sprite/exec",
			wantQuery: map[string][]string{
				"cmd":  {"bash"},
				"path": {"bash"},
				"tty":  {"true"},
				"rows": {"24"},
				"cols": {"80"},
			},
		},
		{
			name:       "command with no stdin",
			spriteName: "my-sprite",
			cmd: &Cmd{
				Path:  "echo",
				Args:  []string{"echo", "hello"},
				Stdin: nil,
			},
			wantPath: "/v1/sprites/my-sprite/exec",
			wantQuery: map[string][]string{
				"cmd":   {"echo", "hello"},
				"path":  {"echo"},
				"stdin": {"false"},
			},
		},
		{
			name:       "command with stdin set",
			spriteName: "my-sprite",
			cmd: &Cmd{
				Path:  "cat",
				Args:  []string{"cat"},
				Stdin: strings.NewReader("test input"),
			},
			wantPath: "/v1/sprites/my-sprite/exec",
			wantQuery: map[string][]string{
				"cmd":   {"cat"},
				"path":  {"cat"},
				"stdin": {"true"},
			},
		},
		{
			name:          "attach with path format (new servers)",
			spriteName:    "my-sprite",
			serverVersion: "0.1.0", // Release version supports path attach
			cmd: &Cmd{
				sessionID: "abc123",
			},
			wantPath: "/v1/sprites/my-sprite/exec/abc123",
			wantQuery: map[string][]string{
				"stdin": {"false"},
			},
		},
		{
			name:              "attach with query format (legacy servers)",
			spriteName:        "my-sprite",
			useLegacyEndpoint: true,
			cmd: &Cmd{
				sessionID: "abc123",
			},
			wantPath: "/v1/sprites/my-sprite/exec",
			wantQuery: map[string][]string{
				"id":    {"abc123"},
				"stdin": {"false"},
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			client := New("test-token", WithBaseURL("http://localhost:8080"))
			if tt.serverVersion != "" {
				client.spriteVersion.Store(tt.serverVersion)
			}
			sprite := client.Sprite(tt.spriteName)
			sprite.useLegacyExecEndpoint = tt.useLegacyEndpoint
			tt.cmd.sprite = sprite

			u, err := tt.cmd.buildWebSocketURL()
			if err != nil {
				t.Fatalf("buildWebSocketURL() error = %v", err)
			}

			// Check scheme conversion
			if u.Scheme != "ws" {
				t.Errorf("scheme = %q, want %q", u.Scheme, "ws")
			}

			// Check path
			if u.Path != tt.wantPath {
				t.Errorf("path = %q, want %q", u.Path, tt.wantPath)
			}

			// Check query parameters
			query := u.Query()
			for key, wantValues := range tt.wantQuery {
				gotValues := query[key]
				if len(gotValues) != len(wantValues) {
					t.Errorf("query[%q] has %d values, want %d", key, len(gotValues), len(wantValues))
					continue
				}
				for i, want := range wantValues {
					if gotValues[i] != want {
						t.Errorf("query[%q][%d] = %q, want %q", key, i, gotValues[i], want)
					}
				}
			}

			// Verify stdin parameter behavior
			// If Stdin is nil, stdin=false should be present
			// If Stdin is set, stdin=true should be present
			stdinParam := query.Get("stdin")
			if tt.cmd.Stdin == nil {
				if stdinParam != "false" {
					t.Errorf("Expected stdin=false when Stdin is nil, got stdin=%q", stdinParam)
				}
			} else {
				if stdinParam != "true" {
					t.Errorf("Expected stdin=true when Stdin is set, got stdin=%q", stdinParam)
				}
			}
		})
	}
}

func TestCmdContextCancellation(t *testing.T) {
	client := New("test-token", WithBaseURL("http://localhost:8080"))
	sprite := client.Sprite("my-sprite")

	// Test that nil context panics
	defer func() {
		if r := recover(); r == nil {
			t.Error("CommandContext with nil context should panic")
		}
	}()

	//nolint:staticcheck // We're testing that nil context panics
	sprite.CommandContext(nil, "echo")
}

func TestExitError(t *testing.T) {
	err := &ExitError{Code: 42}

	if err.Error() != "exit status 42" {
		t.Errorf("Error() = %q, want %q", err.Error(), "exit status 42")
	}

	if err.ExitCode() != 42 {
		t.Errorf("ExitCode() = %d, want %d", err.ExitCode(), 42)
	}

	// Test Sys() returns proper wait status
	if status, ok := err.Sys().(syscall.WaitStatus); ok {
		if status.ExitStatus() != 42 {
			t.Errorf("Sys().ExitStatus() = %d, want %d", status.ExitStatus(), 42)
		}
	} else {
		t.Error("Sys() should return syscall.WaitStatus")
	}
}

func TestCmdValidation(t *testing.T) {
	client := New("test-token", WithBaseURL("http://localhost:8080"))
	sprite := client.Sprite("my-sprite")

	cmd := sprite.Command("echo", "test")

	// Test that various operations succeed before Start
	if _, err := cmd.StdinPipe(); err != nil {
		t.Error("StdinPipe should succeed before Start")
	}

	cmd = sprite.Command("echo", "test")

	if _, err := cmd.StdoutPipe(); err != nil {
		t.Error("StdoutPipe should succeed before Start")
	}

	cmd = sprite.Command("echo", "test")

	if _, err := cmd.StderrPipe(); err != nil {
		t.Error("StderrPipe should succeed before Start")
	}

	// Test double pipe creation fails
	cmd = sprite.Command("echo", "test")
	cmd.Stdin = os.Stdin
	if _, err := cmd.StdinPipe(); err == nil {
		t.Error("StdinPipe should fail when Stdin is already set")
	}

	cmd = sprite.Command("echo", "test")
	cmd.Stdout = os.Stdout
	if _, err := cmd.StdoutPipe(); err == nil {
		t.Error("StdoutPipe should fail when Stdout is already set")
	}

	cmd = sprite.Command("echo", "test")
	cmd.Stderr = os.Stderr
	if _, err := cmd.StderrPipe(); err == nil {
		t.Error("StderrPipe should fail when Stderr is already set")
	}
}

// TestSpriteLifecycle tests the complete lifecycle of a sprite with exec:
// 1. Create a sprite (or use existing if SPRITE_TEST_NAME is set)
// 2. Run exec commands on it
// 3. Destroy the sprite (unless SPRITE_TEST_NAME is set)
func TestSpriteLifecycle(t *testing.T) {
	// Skip if no test token is provided
	token := os.Getenv("SPRITES_TEST_TOKEN")
	if token == "" {
		t.Skip("SPRITES_TEST_TOKEN environment variable not set")
	}

	// Create client
	client := New(token)

	// Check if we should use an existing sprite or create a new one
	spriteName := os.Getenv("SPRITE_TEST_NAME")
	useExistingSprite := spriteName != ""

	if !useExistingSprite {
		// Generate unique sprite name to avoid conflicts
		spriteName = fmt.Sprintf("test-sprite-%d", time.Now().UnixNano())
	} else {
		t.Logf("Using existing sprite: %s", spriteName)
	}

	// Test 1: Create sprite (skip if using existing sprite)
	if !useExistingSprite {
		t.Run("CreateSprite", func(t *testing.T) {
			ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
			defer cancel()

			sprite, err := client.CreateSprite(ctx, spriteName, nil)
			if err != nil {
				t.Fatalf("Failed to create sprite: %v", err)
			}

			if sprite.Name() != spriteName {
				t.Errorf("Expected sprite name %q, got %q", spriteName, sprite.Name())
			}

			// Verify sprite was created by getting it
			retrievedSprite, err := client.GetSprite(ctx, spriteName)
			if err != nil {
				t.Fatalf("Failed to retrieve created sprite: %v", err)
			}

			if retrievedSprite.Name() != spriteName {
				t.Errorf("Expected retrieved sprite name %q, got %q", spriteName, retrievedSprite.Name())
			}

			t.Logf("Successfully created sprite: %s", spriteName)
		})
	} else {
		t.Logf("Skipping sprite creation (using existing sprite from SPRITE_TEST_NAME: %s)", spriteName)
	}

	// Test 2: Run exec commands
	t.Run("ExecCommands", func(t *testing.T) {
		ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer cancel()

		sprite := client.Sprite(spriteName)

		// Test simple echo command
		t.Run("EchoCommand", func(t *testing.T) {
			cmd := sprite.CommandContext(ctx, "echo", "hello", "world")
			output, err := cmd.Output()
			if err != nil {
				t.Fatalf("Echo command failed: %v", err)
			}

			expected := "hello world\n"
			if string(output) != expected {
				t.Errorf("Expected output %q, got %q", expected, string(output))
			}

			t.Logf("Echo command output: %q", string(output))
		})

		// Test pwd command
		t.Run("PwdCommand", func(t *testing.T) {
			cmd := sprite.CommandContext(ctx, "pwd")
			output, err := cmd.Output()
			if err != nil {
				t.Fatalf("Pwd command failed: %v", err)
			}

			// Should be in the home directory
			if !strings.Contains(string(output), "/home") {
				t.Errorf("Expected pwd to contain /home, got %q", string(output))
			}

			t.Logf("Pwd command output: %q", string(output))
		})

		// Test command with environment variables
		t.Run("EnvCommand", func(t *testing.T) {
			cmd := sprite.CommandContext(ctx, "env")
			cmd.Env = []string{"TEST_VAR=hello", "ANOTHER_VAR=world"}
			output, err := cmd.Output()
			if err != nil {
				t.Fatalf("Env command failed: %v", err)
			}

			outputStr := string(output)
			if !strings.Contains(outputStr, "TEST_VAR=hello") {
				t.Error("Expected output to contain TEST_VAR=hello")
			}
			if !strings.Contains(outputStr, "ANOTHER_VAR=world") {
				t.Error("Expected output to contain ANOTHER_VAR=world")
			}

			t.Logf("Env command found expected variables")
		})

		// Test command with working directory
		t.Run("DirCommand", func(t *testing.T) {
			cmd := sprite.CommandContext(ctx, "pwd")
			cmd.Dir = "/tmp"
			output, err := cmd.Output()
			if err != nil {
				t.Fatalf("Dir command failed: %v", err)
			}

			expected := "/tmp\n"
			if string(output) != expected {
				t.Errorf("Expected output %q, got %q", expected, string(output))
			}

			t.Logf("Dir command output: %q", string(output))
		})

		// Test command that returns non-zero exit code
		t.Run("ErrorCommand", func(t *testing.T) {
			cmd := sprite.CommandContext(ctx, "sh", "-c", "exit 42")
			err := cmd.Run()
			if err == nil {
				t.Error("Expected command to return error")
			}

			exitErr, ok := err.(*ExitError)
			if !ok {
				t.Errorf("Expected ExitError, got %T", err)
			} else if exitErr.ExitCode() != 42 {
				t.Errorf("Expected exit code 42, got %d", exitErr.ExitCode())
			} else {
				t.Logf("Error command failed as expected with exit code %d", exitErr.ExitCode())
			}
		})

		// Test command with pipes
		t.Run("PipeCommand", func(t *testing.T) {
			cmd := sprite.CommandContext(ctx, "cat")

			// Set up stdin pipe
			stdin, err := cmd.StdinPipe()
			if err != nil {
				t.Fatalf("Failed to create stdin pipe: %v", err)
			}

			// Start command
			err = cmd.Start()
			if err != nil {
				t.Fatalf("Failed to start command: %v", err)
			}

			// Write to stdin
			testInput := "hello from pipe test\n"
			_, err = stdin.Write([]byte(testInput))
			if err != nil {
				t.Fatalf("Failed to write to stdin: %v", err)
			}
			stdin.Close()

			// Wait for command to complete
			err = cmd.Wait()
			if err != nil {
				t.Fatalf("Command failed: %v", err)
			}

			t.Logf("Pipe test completed successfully")
		})

		// Test TTY mode with tty command
		t.Run("TTYCommand", func(t *testing.T) {
			cmd := sprite.CommandContext(ctx, "tty")
			cmd.SetTTY(true)
			cmd.SetTTYSize(24, 80)

			output, err := cmd.Output()
			if err != nil {
				t.Fatalf("TTY command failed: %v", err)
			}

			outputStr := string(output)
			// When TTY mode is enabled, tty command should output a device path
			if !strings.Contains(outputStr, "/dev/") {
				t.Errorf("Expected TTY output to contain /dev/, got %q", outputStr)
			}

			t.Logf("TTY command output: %q", outputStr)
		})

		// Test non-TTY mode
		t.Run("NonTTYCommand", func(t *testing.T) {
			cmd := sprite.CommandContext(ctx, "tty")
			// Don't enable TTY mode

			output, err := cmd.CombinedOutput()
			// tty command exits with status 1 when not connected to a tty
			if err != nil {
				if exitErr, ok := err.(*ExitError); !ok || exitErr.ExitCode() != 1 {
					t.Fatalf("Non-TTY command failed with unexpected error: %v", err)
				}
			}

			outputStr := string(output)
			// When TTY mode is disabled, tty command should output "not a tty"
			if !strings.Contains(outputStr, "not a tty") {
				t.Errorf("Expected non-TTY output to contain 'not a tty', got %q", outputStr)
			}

			t.Logf("Non-TTY command output: %q", outputStr)
		})

		// Test interactive command with TTY
		t.Run("InteractiveCommand", func(t *testing.T) {
			// Test that a command requiring TTY works (e.g., reading terminal size)
			cmd := sprite.CommandContext(ctx, "sh", "-c", "stty size")
			cmd.SetTTY(true)
			cmd.SetTTYSize(24, 80)

			output, err := cmd.Output()
			if err != nil {
				t.Fatalf("Interactive TTY command failed: %v", err)
			}

			outputStr := strings.TrimSpace(string(output))
			// stty size should output "24 80" when TTY is set to those dimensions
			if outputStr != "24 80" {
				t.Errorf("Expected stty size to output '24 80', got %q", outputStr)
			}

			t.Logf("Terminal size output: %q", outputStr)
		})
	})

	// Test 3: Destroy sprite (skip if using existing sprite)
	if !useExistingSprite {
		t.Run("DestroySprite", func(t *testing.T) {
			ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
			defer cancel()

			err := client.DeleteSprite(ctx, spriteName)
			if err != nil {
				t.Fatalf("Failed to destroy sprite: %v", err)
			}

			// Verify sprite was destroyed by trying to get it
			_, err = client.GetSprite(ctx, spriteName)
			if err == nil {
				t.Error("Expected sprite to be deleted, but GetSprite succeeded")
			} else {
				// Sprite was successfully deleted, we expect some kind of error
				t.Logf("Sprite deletion verified (got expected error: %v)", err)
			}

			t.Logf("Successfully destroyed sprite: %s", spriteName)
		})
	} else {
		t.Logf("Skipping sprite destruction (using existing sprite from SPRITE_TEST_NAME: %s)", spriteName)
	}
}
