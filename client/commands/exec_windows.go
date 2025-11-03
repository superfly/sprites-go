//go:build windows

package commands

import (
	"os"
	"time"

	sprites "github.com/superfly/sprites-go"
	"golang.org/x/term"
)

// handleSpriteTerminalResize polls for size changes on Windows, where SIGWINCH is unavailable
func handleSpriteTerminalResize(cmd *sprites.Cmd) {
	// The Go term package's GetSize works on Windows, but there's no signal,
	// so we do a light polling loop with debounce.
	var lastW, lastH int
	ticker := time.NewTicker(300 * time.Millisecond)
	defer ticker.Stop()
	for range ticker.C {
		// Note: we can't reliably detect terminal-ness on Windows consoles the same way;
		// keep polling and attempt SetTTYSize when size changes.
		w, h, err := getTerminalSizeWindows()
		if err != nil {
			continue
		}
		if w == lastW && h == lastH {
			continue
		}
		lastW, lastH = w, h
		_ = cmd.SetTTYSize(uint16(h), uint16(w))
	}
}

func getTerminalSizeWindows() (int, int, error) {
	return term.GetSize(int(os.Stdin.Fd()))
}
