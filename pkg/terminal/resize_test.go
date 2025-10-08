package terminal

import (
	"os"
	"testing"

	creackpty "github.com/creack/pty"
)

func TestResizeTerminal(t *testing.T) {
	// PTY is always available in Docker test environment

	// Create a temporary PTY for testing
	pty, tty, err := openPty()
	if err != nil {
		t.Fatalf("Could not create PTY for testing: %v - test environment is misconfigured", err)
	}
	defer pty.Close()
	defer tty.Close()

	// Test resizing
	err = ResizeTerminal(pty, 100, 50)
	if err != nil {
		t.Errorf("ResizeTerminal failed: %v", err)
	}

	// Get the size back and verify
	cols, rows, err := GetTerminalSize(pty)
	if err != nil {
		t.Errorf("GetTerminalSize failed: %v", err)
	}

	if cols != 100 || rows != 50 {
		t.Errorf("expected size 100x50, got %dx%d", cols, rows)
	}
}

func TestGetTerminalSize(t *testing.T) {
	// PTY is always available in Docker test environment

	// Create a temporary PTY for testing
	pty, tty, err := openPty()
	if err != nil {
		t.Fatalf("Could not create PTY for testing: %v - test environment is misconfigured", err)
	}
	defer pty.Close()
	defer tty.Close()

	// Set an initial size so we can test getting it back
	err = ResizeTerminal(pty, 80, 24)
	if err != nil {
		t.Fatalf("ResizeTerminal failed: %v", err)
	}

	// Get the size back
	cols, rows, err := GetTerminalSize(pty)
	if err != nil {
		t.Errorf("GetTerminalSize failed: %v", err)
	}

	// Verify we got the size we set
	if cols != 80 || rows != 24 {
		t.Errorf("expected size 80x24, got %dx%d", cols, rows)
	}
}

// openPty creates a PTY for testing purposes
func openPty() (*os.File, *os.File, error) {
	return creackpty.Open()
}
