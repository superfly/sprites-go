package terminal

import (
	"bufio"
	"context"
	"fmt"
	"io"
	"os"
	"os/exec"
	"strings"
	"sync"
	"time"
)

// TranscriptReader provides a unified interface for reading transcript data
// in both post-mortem and live streaming modes.
type TranscriptReader interface {
	// NextLine returns the next line from the transcript.
	// Returns io.EOF when the transcript is complete and no more lines are available.
	// For live streams, this method blocks until a line is available or the context is cancelled.
	NextLine(ctx context.Context) (string, error)

	// Close releases any resources associated with the reader.
	Close() error
}

// TranscriptReaderConfig holds configuration options for transcript readers.
type TranscriptReaderConfig struct {
	// BufferSize controls the internal line buffer size for live streams (default: 100)
	BufferSize int
	// FlushInterval controls how often buffered lines are made available (default: 1s)
	FlushInterval time.Duration
	// Stream specifies which stream to read ("stdout", "stderr", "all"). Default: "all"
	Stream string
}

// DefaultTranscriptReaderConfig returns the default configuration.
func DefaultTranscriptReaderConfig() TranscriptReaderConfig {
	return TranscriptReaderConfig{
		BufferSize:    100,
		FlushInterval: time.Second,
		Stream:        "all",
	}
}

// OpenTranscript opens a completed transcript file for post-mortem reading.
// The file should be in the structured log format created by FileTranscript.
func OpenTranscript(path string) (TranscriptReader, error) {
	return OpenTranscriptWithConfig(path, DefaultTranscriptReaderConfig())
}

// OpenTranscriptWithConfig opens a transcript file with custom configuration.
func OpenTranscriptWithConfig(path string, config TranscriptReaderConfig) (TranscriptReader, error) {
	file, err := os.Open(path)
	if err != nil {
		return nil, fmt.Errorf("failed to open transcript file: %w", err)
	}

	return &fileTranscriptReader{
		file:    file,
		config:  config,
		scanner: bufio.NewScanner(file),
	}, nil
}

// StreamTranscript creates a live transcript reader that streams output from a running command.
// The reader will continue to provide lines until the command exits or the context is cancelled.
func StreamTranscript(ctx context.Context, cmd *exec.Cmd) (TranscriptReader, error) {
	return StreamTranscriptWithConfig(ctx, cmd, DefaultTranscriptReaderConfig())
}

// StreamTranscriptWithConfig creates a live transcript reader with custom configuration.
func StreamTranscriptWithConfig(ctx context.Context, cmd *exec.Cmd, config TranscriptReaderConfig) (TranscriptReader, error) {
	reader := &liveTranscriptReader{
		config:    config,
		linesChan: make(chan string, config.BufferSize),
		errorChan: make(chan error, 1),
		doneChan:  make(chan struct{}),
	}

	// Start the command and capture its output
	if err := reader.startCapture(ctx, cmd); err != nil {
		return nil, fmt.Errorf("failed to start transcript capture: %w", err)
	}

	return reader, nil
}

// StreamMemoryTranscript creates a live transcript reader from a MemoryTranscript.
// This is useful for testing or when you want to stream from an existing memory transcript.
func StreamMemoryTranscript(ctx context.Context, transcript *MemoryTranscript) TranscriptReader {
	return StreamMemoryTranscriptWithConfig(ctx, transcript, DefaultTranscriptReaderConfig())
}

// StreamMemoryTranscriptWithConfig creates a live transcript reader from a MemoryTranscript with custom config.
func StreamMemoryTranscriptWithConfig(ctx context.Context, transcript *MemoryTranscript, config TranscriptReaderConfig) TranscriptReader {
	reader := &memoryTranscriptReader{
		transcript: transcript,
		config:     config,
		position:   make(map[string]int),
	}

	reader.startReading(ctx)
	return reader
}

// fileTranscriptReader implements TranscriptReader for completed transcript files.
type fileTranscriptReader struct {
	file    *os.File
	config  TranscriptReaderConfig
	scanner *bufio.Scanner
	mu      sync.Mutex
}

func (r *fileTranscriptReader) NextLine(ctx context.Context) (string, error) {
	r.mu.Lock()
	defer r.mu.Unlock()

	// Check for context cancellation
	select {
	case <-ctx.Done():
		return "", ctx.Err()
	default:
	}

	for r.scanner.Scan() {
		line := r.scanner.Text()

		// Parse the structured log line to extract transcript content
		if transcriptLine := r.parseLogLine(line); transcriptLine != "" {
			return transcriptLine, nil
		}
	}

	if err := r.scanner.Err(); err != nil {
		return "", fmt.Errorf("scan error: %w", err)
	}

	return "", io.EOF
}

func (r *fileTranscriptReader) parseLogLine(line string) string {
	// Parse structured log format: time=... level=... msg=io stream=... line=...
	// Extract the line= field if stream matches our filter
	parts := strings.Fields(line)
	var stream, content string

	for _, part := range parts {
		if strings.HasPrefix(part, "stream=") {
			stream = strings.TrimPrefix(part, "stream=")
		} else if strings.HasPrefix(part, "line=") {
			content = strings.TrimPrefix(part, "line=")
			// Handle quoted content
			if strings.HasPrefix(content, `"`) && strings.HasSuffix(content, `"`) {
				content = content[1 : len(content)-1]
			}
		}
	}

	// Filter by stream if specified
	if r.config.Stream != "all" && stream != r.config.Stream {
		return ""
	}

	return content
}

func (r *fileTranscriptReader) Close() error {
	if r.file != nil {
		return r.file.Close()
	}
	return nil
}

// liveTranscriptReader implements TranscriptReader for live command output streaming.
type liveTranscriptReader struct {
	config    TranscriptReaderConfig
	linesChan chan string
	errorChan chan error
	doneChan  chan struct{}
	cmd       *exec.Cmd
	mu        sync.Mutex
	closed    bool
}

func (r *liveTranscriptReader) startCapture(ctx context.Context, cmd *exec.Cmd) error {
	r.cmd = cmd

	// Set up stdout and stderr pipes
	stdoutPipe, err := cmd.StdoutPipe()
	if err != nil {
		return fmt.Errorf("failed to create stdout pipe: %w", err)
	}

	stderrPipe, err := cmd.StderrPipe()
	if err != nil {
		return fmt.Errorf("failed to create stderr pipe: %w", err)
	}

	// Start the command
	if err := cmd.Start(); err != nil {
		return fmt.Errorf("failed to start command: %w", err)
	}

	// Start goroutines to capture output
	var wg sync.WaitGroup

	if r.config.Stream == "all" || r.config.Stream == "stdout" {
		wg.Add(1)
		go r.captureStream(ctx, "stdout", stdoutPipe, &wg)
	}

	if r.config.Stream == "all" || r.config.Stream == "stderr" {
		wg.Add(1)
		go r.captureStream(ctx, "stderr", stderrPipe, &wg)
	}

	// Wait for command to complete and close channels
	go func() {
		defer close(r.doneChan)
		defer close(r.linesChan)

		wg.Wait()
		cmd.Wait()
	}()

	return nil
}

func (r *liveTranscriptReader) captureStream(ctx context.Context, streamName string, pipe io.ReadCloser, wg *sync.WaitGroup) {
	defer wg.Done()
	defer pipe.Close()

	scanner := bufio.NewScanner(pipe)
	for scanner.Scan() {
		select {
		case <-ctx.Done():
			return
		case r.linesChan <- scanner.Text():
		}
	}

	if err := scanner.Err(); err != nil {
		select {
		case <-ctx.Done():
		case r.errorChan <- fmt.Errorf("scan error on %s: %w", streamName, err):
		}
	}
}

func (r *liveTranscriptReader) NextLine(ctx context.Context) (string, error) {
	r.mu.Lock()
	closed := r.closed
	r.mu.Unlock()

	if closed {
		return "", io.EOF
	}

	select {
	case <-ctx.Done():
		return "", ctx.Err()
	case line, ok := <-r.linesChan:
		if !ok {
			return "", io.EOF
		}
		return line, nil
	case err := <-r.errorChan:
		return "", err
	}
}

func (r *liveTranscriptReader) Close() error {
	r.mu.Lock()
	defer r.mu.Unlock()

	if r.closed {
		return nil
	}
	r.closed = true

	if r.cmd != nil && r.cmd.Process != nil {
		r.cmd.Process.Kill()
	}

	return nil
}

// memoryTranscriptReader implements TranscriptReader for MemoryTranscript streaming.
type memoryTranscriptReader struct {
	transcript *MemoryTranscript
	config     TranscriptReaderConfig
	position   map[string]int
	linesChan  chan string
	doneChan   chan struct{}
	mu         sync.Mutex
	closed     bool
}

func (r *memoryTranscriptReader) startReading(ctx context.Context) {
	r.linesChan = make(chan string, r.config.BufferSize)
	r.doneChan = make(chan struct{})

	go func() {
		defer close(r.linesChan)
		defer close(r.doneChan)

		ticker := time.NewTicker(r.config.FlushInterval)
		defer ticker.Stop()

		for {
			select {
			case <-ctx.Done():
				return
			case <-ticker.C:
				r.flushNewLines()
			}
		}
	}()
}

func (r *memoryTranscriptReader) flushNewLines() {
	r.mu.Lock()
	defer r.mu.Unlock()

	if r.closed {
		return
	}

	// Get streams to read based on config
	streams := []string{}
	if r.config.Stream == "all" {
		streams = []string{"stdout", "stderr"}
	} else {
		streams = []string{r.config.Stream}
	}

	for _, stream := range streams {
		data := r.transcript.GetStreamData(stream)
		if data == nil {
			continue
		}

		// Convert to lines and send new ones
		lines := strings.Split(string(data), "\n")
		currentPos := r.position[stream]

		for i := currentPos; i < len(lines)-1; i++ { // -1 to avoid empty line at end
			select {
			case r.linesChan <- lines[i]:
			default:
				// Channel full, skip
				return
			}
		}

		r.position[stream] = len(lines) - 1
	}
}

func (r *memoryTranscriptReader) NextLine(ctx context.Context) (string, error) {
	r.mu.Lock()
	closed := r.closed
	r.mu.Unlock()

	if closed {
		return "", io.EOF
	}

	select {
	case <-ctx.Done():
		return "", ctx.Err()
	case line, ok := <-r.linesChan:
		if !ok {
			return "", io.EOF
		}
		return line, nil
	}
}

func (r *memoryTranscriptReader) Close() error {
	r.mu.Lock()
	defer r.mu.Unlock()

	if r.closed {
		return nil
	}
	r.closed = true
	return nil
}
