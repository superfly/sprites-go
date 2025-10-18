package container

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"log/slog"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
)

// WrapConfig holds configuration for wrapping a command
type WrapConfig struct {
	tty           bool
	consoleSocket string
	ttyManager    *Tty // TTY manager for console socket (only for TTY mode)
}

// WrapOption configures command wrapping
type WrapOption func(*WrapConfig)

// WithTTY enables TTY mode with console socket
func WithTTY(enabled bool) WrapOption {
	return func(c *WrapConfig) {
		c.tty = enabled
	}
}

// WithConsoleSocket sets a custom console socket path
func WithConsoleSocket(path string) WrapOption {
	return func(c *WrapConfig) {
		c.consoleSocket = path
	}
}

// WrappedCommand holds a wrapped command and provides access to the PTY file for TTY mode
type WrappedCommand struct {
	*exec.Cmd
	config *WrapConfig
}

// GetPTY waits for and returns the PTY file from the console socket
// This should be called after Start() for TTY mode commands
// Returns nil if not in TTY mode
func (w *WrappedCommand) GetPTY() (*os.File, error) {
	if !w.config.tty || w.config.ttyManager == nil {
		return nil, nil
	}
	return w.config.ttyManager.Get()
}

// ClosePTY closes the PTY manager and cleans up resources
func (w *WrappedCommand) ClosePTY() error {
	if w.config.ttyManager != nil {
		return w.config.ttyManager.Close()
	}
	return nil
}

// Wrap builds/uses a hashed process.json and returns a crun exec command
func Wrap(cmd *exec.Cmd, containerName string, opts ...WrapOption) *WrappedCommand {
	config := &WrapConfig{}
	for _, opt := range opts {
		opt(config)
	}

	tmpl, err := CloneProcessTemplate()
	if err != nil {
		slog.Error("container.Wrap: process template not loaded; cannot exec", "error", err)
		return &WrappedCommand{Cmd: exec.Command("false"), config: config}
	}

	spec := &ProcessSpec{
		Terminal: config.tty,
		Cwd:      tmpl.Cwd,
		Env:      mergeEnv(tmpl.Env, cmd.Env),
		Args:     nil,
	}
	if cmd.Dir != "" {
		spec.Cwd = cmd.Dir
	}
	spec.Args = append([]string{cmd.Path}, cmd.Args[1:]...)

	// Stable hash of spec
	hasher := sha256.New()
	if spec.Terminal {
		_, _ = hasher.Write([]byte("tty=1;"))
	} else {
		_, _ = hasher.Write([]byte("tty=0;"))
	}
	_, _ = hasher.Write([]byte("cwd=" + spec.Cwd + ";"))
	envCopy := append([]string(nil), spec.Env...)
	sort.Strings(envCopy)
	for _, e := range envCopy {
		_, _ = hasher.Write([]byte("env=" + e + ";"))
	}
	for _, a := range spec.Args {
		_, _ = hasher.Write([]byte("arg=" + a + ";"))
	}
	sum := hex.EncodeToString(hasher.Sum(nil))

	dir := "/.sprite/tmp/.crun"
	if err := os.MkdirAll(dir, 0755); err != nil {
		slog.Error("container.Wrap: failed to create process dir", "error", err)
		return &WrappedCommand{Cmd: exec.Command("false"), config: config}
	}
	procPath := filepath.Join(dir, "process-"+sum+".json")
	if _, statErr := os.Stat(procPath); os.IsNotExist(statErr) {
		data, mErr := json.Marshal(spec)
		if mErr != nil {
			slog.Error("container.Wrap: failed to marshal process spec", "error", mErr)
			return &WrappedCommand{Cmd: exec.Command("false"), config: config}
		}
		if wErr := os.WriteFile(procPath, data, 0644); wErr != nil {
			slog.Error("container.Wrap: failed to write process.json", "error", wErr, "path", procPath)
			return &WrappedCommand{Cmd: exec.Command("false"), config: config}
		}
	}

	args := []string{"exec"}
	if config.tty {
		if config.consoleSocket == "" {
			config.consoleSocket = generateSocketPath()
		}
		args = append(args, "--tty", "--console-socket", config.consoleSocket)
	}
	args = append(args, "--process", procPath)
	args = append(args, containerName)

	wrapped := exec.Command("crun", args...)
	wrapped.Env = os.Environ()
	wrapped.Stdin = cmd.Stdin
	wrapped.Stdout = cmd.Stdout
	wrapped.Stderr = cmd.Stderr
	if cmd.Cancel != nil {
		wrapped.Cancel = cmd.Cancel
	}

	if config.tty {
		if tty, err := NewWithPath(config.consoleSocket); err == nil {
			config.ttyManager = tty
		}
	}

	wc := &WrappedCommand{Cmd: wrapped, config: config}
	slog.Debug("container.Wrap: built crun exec command",
		"fullCommand", wrapped.String(),
		"path", wrapped.Path,
		"args", wrapped.Args,
		"process", procPath)
	return wc
}

// generateSocketPath creates a unique socket path for console socket
func generateSocketPath() string {
	socketDir := GetSocketDir()
	return fmt.Sprintf("%s/console-%d.sock", socketDir, os.Getpid())
}

// GetPTYFunc returns a function suitable for runner.WithWaitTTY that fetches
// the PTY file from the wrapped command's console socket.
//
// The returned function should be invoked after the wrapped command has been started.
func GetPTYFunc(socketPath string) func(ctx context.Context) (*os.File, error) {
	return func(ctx context.Context) (*os.File, error) {
		tty, err := NewWithPath(socketPath)
		if err != nil {
			return nil, err
		}
		defer tty.Close()
		return tty.Get()
	}
}

// WrapForUser wraps a user command to execute inside a container using a per-command process.json
// built from the immutable template loaded at boot.
// Remove legacy wrappers; callers must use Wrap
