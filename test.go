package sprites

import (
	"os"
	"syscall"
	"testing"
)

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
		name       string
		spriteName string
		cmd        *Cmd
		wantPath   string
		wantQuery  map[string][]string
	}{
		{
			name:       "basic command",
			spriteName: "my-sprite",
			cmd: &Cmd{
				Path: "echo",
				Args: []string{"echo", "hello"},
			},
			wantPath: "/sprites/my-sprite/exec",
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
			wantPath: "/sprites/test-sprite/exec",
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
			wantPath: "/sprites/my-sprite/exec",
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
			wantPath: "/sprites/my-sprite/exec",
			wantQuery: map[string][]string{
				"cmd":  {"bash"},
				"path": {"bash"},
				"tty":  {"true"},
				"rows": {"24"},
				"cols": {"80"},
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			client := New("test-token", WithBaseURL("http://localhost:8080"))
			sprite := client.Sprite(tt.spriteName)
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

func TestClientOptions(t *testing.T) {
	// Test default client
	client := New("test-token")
	if client.baseURL != "https://api.sprite.dev" {
		t.Errorf("default baseURL = %q, want %q", client.baseURL, "https://api.sprite.dev")
	}
	if client.token != "test-token" {
		t.Errorf("token = %q, want %q", client.token, "test-token")
	}

	// Test with custom base URL
	client = New("test-token", WithBaseURL("http://localhost:8080"))
	if client.baseURL != "http://localhost:8080" {
		t.Errorf("custom baseURL = %q, want %q", client.baseURL, "http://localhost:8080")
	}
}
