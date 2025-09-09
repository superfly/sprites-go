package tmux

import (
	"bufio"
	"fmt"
	"io"
	"log/slog"
	"os/exec"
	"strings"
	"sync"
	"time"
)

// stderrLogger writes tmux stderr output to slog
type stderrLogger struct {
	logger *slog.Logger
}

func (w *stderrLogger) Write(p []byte) (int, error) {
	lines := strings.Split(strings.TrimRight(string(p), "\n"), "\n")
	for _, line := range lines {
		if line != "" {
			w.logger.Warn("tmux stderr", "output", line)
		}
	}
	return len(p), nil
}

// TmuxControlModeParser parses tmux control mode output
type TmuxControlModeParser struct {
	// Window and pane tracking
	windows       map[string]*TmuxWindow // windowID -> window
	panes         map[string]*TmuxPane   // paneID -> pane
	unmappedPanes map[string]*TmuxPane   // panes without known windows

	// Current pending command
	pendingCommand string

	// Event channel
	events chan TmuxEvent

	// Data rate tracking
	dataRateWindow time.Duration

	// Process management
	cmd    *exec.Cmd
	stdin  io.WriteCloser
	stdout io.ReadCloser
	done   chan error
	once   sync.Once
}

// NewTmuxControlModeParser creates a new parser instance that manages a tmux control mode process.
// The command should be configured to run tmux with either:
// - `-C` flag: Control mode with echo enabled (easier for debugging)
// - `-CC` flag: Control mode with echo disabled (cleaner output but harder to debug)
// If logger is provided, stderr output will be logged. If nil, stderr will be discarded.
func NewTmuxControlModeParser(cmd *exec.Cmd, logger *slog.Logger) (*TmuxControlModeParser, error) {
	if logger != nil {
		logger.Debug("Creating TmuxControlModeParser",
			"cmd", cmd.String())
	}
	// Get pipes directly from the command
	stdin, err := cmd.StdinPipe()
	if err != nil {
		return nil, fmt.Errorf("failed to get stdin pipe: %w", err)
	}

	stdout, err := cmd.StdoutPipe()
	if err != nil {
		return nil, fmt.Errorf("failed to get stdout pipe: %w", err)
	}

	// Set up stderr logging
	if logger != nil {
		cmd.Stderr = &stderrLogger{logger: logger}
	}

	// Start the command
	if logger != nil {
		logger.Debug("Starting tmux command")
	}
	if err := cmd.Start(); err != nil {
		if logger != nil {
			logger.Error("Failed to start tmux command",
				"error", err,
				"cmd", cmd.String())
		}
		return nil, fmt.Errorf("failed to start tmux: %w", err)
	}
	if logger != nil {
		logger.Debug("Tmux command started successfully",
			"pid", cmd.Process.Pid)
	}

	parser := &TmuxControlModeParser{
		windows:        make(map[string]*TmuxWindow),
		panes:          make(map[string]*TmuxPane),
		unmappedPanes:  make(map[string]*TmuxPane),
		events:         make(chan TmuxEvent, 10000), // Large buffer for continuous output events
		dataRateWindow: 5 * time.Second,
		cmd:            cmd,
		stdin:          stdin,
		stdout:         stdout,
		done:           make(chan error, 1),
	}

	// Start reading stdout
	go parser.readLoop()

	return parser, nil
}

// readLoop reads from stdout and processes lines
func (p *TmuxControlModeParser) readLoop() {
	defer func() {
		// Close events channel when done
		close(p.events)
		// Send the wait result
		select {
		case p.done <- p.cmd.Wait():
		default:
		}
		close(p.done)
	}()

	scanner := bufio.NewScanner(p.stdout)
	for scanner.Scan() {
		line := scanner.Text()
		p.ParseLine(line)
	}

	// If scanner encountered an error, send it
	if err := scanner.Err(); err != nil {
		select {
		case p.done <- err:
		default:
		}
	}
}

// Wait waits for the tmux process to exit
func (p *TmuxControlModeParser) Wait() error {
	return <-p.done
}

// Close closes the parser and kills the tmux process
func (p *TmuxControlModeParser) Close() error {
	p.once.Do(func() {
		p.stdin.Close()
		p.stdout.Close()
		p.cmd.Process.Kill()
	})
	return p.Wait()
}

// Stdin returns the stdin pipe for sending commands
func (p *TmuxControlModeParser) Stdin() io.WriteCloser {
	return p.stdin
}

// Stdout returns the stdout pipe (mostly for debugging)
func (p *TmuxControlModeParser) Stdout() io.ReadCloser {
	return p.stdout
}

// Events returns the event channel
func (p *TmuxControlModeParser) Events() <-chan TmuxEvent {
	return p.events
}

// SendCommand sends a command to tmux
func (p *TmuxControlModeParser) SendCommand(command string) error {
	_, err := fmt.Fprintf(p.stdin, "%s\n", command)
	return err
}

// GetWindow returns a window by ID
func (p *TmuxControlModeParser) GetWindow(windowID string) (*TmuxWindow, bool) {
	window, ok := p.windows[windowID]
	return window, ok
}

// GetPane returns a pane by ID
func (p *TmuxControlModeParser) GetPane(paneID string) (*TmuxPane, bool) {
	pane, ok := p.panes[paneID]
	return pane, ok
}

// GetUnmappedPanes returns all panes not currently mapped to windows
func (p *TmuxControlModeParser) GetUnmappedPanes() []*TmuxPane {
	result := make([]*TmuxPane, 0, len(p.unmappedPanes))
	for _, pane := range p.unmappedPanes {
		result = append(result, pane)
	}
	return result
}

// ListWindows sends the list-windows command
func (p *TmuxControlModeParser) ListWindows() error {
	return p.SendCommand("list-windows")
}

// ListPanes sends the list-panes command
func (p *TmuxControlModeParser) ListPanes() error {
	return p.SendCommand("list-panes -a")
}

// RefreshWindowsAndPanes refreshes both windows and panes
func (p *TmuxControlModeParser) RefreshWindowsAndPanes() error {
	if err := p.ListWindows(); err != nil {
		return err
	}
	return p.ListPanes()
}
