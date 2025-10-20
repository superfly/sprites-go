//go:build unix && !windows

package commands

import (
	"os"
	"os/signal"
	"syscall"

	sprites "github.com/superfly/sprites-go"
	"golang.org/x/term"
)

// handleSpriteTerminalResize monitors for terminal resize events on Unix and updates the remote TTY size
func handleSpriteTerminalResize(cmd *sprites.Cmd) {
	if !term.IsTerminal(int(os.Stdin.Fd())) {
		return
	}

	if w, h, err := term.GetSize(int(os.Stdin.Fd())); err == nil {
		_ = cmd.SetTTYSize(uint16(h), uint16(w))
	}

	ch := make(chan os.Signal, 1)
	signal.Notify(ch, syscall.SIGWINCH)
	defer signal.Stop(ch)

	var lastW, lastH int
	for {
		<-ch
		if !term.IsTerminal(int(os.Stdin.Fd())) {
			continue
		}
		w, h, err := term.GetSize(int(os.Stdin.Fd()))
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
