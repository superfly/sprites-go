//go:build !windows
// +build !windows

package commands

import (
	"os"
	"os/signal"
	"syscall"

	"github.com/superfly/sprite-env/pkg/terminal"
	"golang.org/x/term"
)

// handleTerminalResize sets up terminal resize handling for Unix systems
func handleTerminalResize(wsCmd *terminal.Cmd) {
	sigCh := make(chan os.Signal, 1)
	signal.Notify(sigCh, syscall.SIGWINCH)

	go func() {
		for range sigCh {
			// Get current terminal size and send to server
			width, height, err := term.GetSize(int(os.Stdin.Fd()))
			if err == nil {
				wsCmd.Resize(uint16(width), uint16(height))
			}
		}
	}()
}
