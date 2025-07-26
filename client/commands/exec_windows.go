//go:build windows
// +build windows

package commands

import (
	"github.com/superfly/sprite-env/pkg/terminal"
)

// handleTerminalResize sets up terminal resize handling for Windows
func handleTerminalResize(wsCmd *terminal.Cmd) {
	// On Windows, terminal resize is handled differently
	// Windows Terminal and ConPTY handle this automatically through the console API
	// We don't need to set up SIGWINCH handling

	// The initial size is already sent when the connection is established
	// And Windows will handle subsequent resize events through the console API
}
