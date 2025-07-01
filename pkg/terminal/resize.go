package terminal

import (
	"os"

	creackpty "github.com/creack/pty"
)

// ResizeTerminal resizes a PTY to the specified dimensions.
// This function can be called from external code to handle resize events.
func ResizeTerminal(pty *os.File, cols, rows uint16) error {
	return creackpty.Setsize(pty, &creackpty.Winsize{
		Cols: cols,
		Rows: rows,
	})
}

// GetTerminalSize returns the current size of a PTY.
func GetTerminalSize(pty *os.File) (cols, rows uint16, err error) {
	size, err := creackpty.GetsizeFull(pty)
	if err != nil {
		return 0, 0, err
	}
	return size.Cols, size.Rows, nil
}
