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
	"sync/atomic"
	"time"

	"github.com/google/uuid"
)

// TranscriptLine represents a single line from a transcript with metadata.
type TranscriptLine struct {
	// SessionID uniquely identifies the session this line belongs to
	SessionID string `json:"session_id"`
	// Sequence is the line number within the session (starts at 1)
	Sequence int64 `json:"sequence"`
	// Timestamp when the line was recorded
	Timestamp time.Time `json:"timestamp"`
	// Stream identifies the I/O stream ("stdin", "stdout", "stderr")
	Stream string `json:"stream"`
	// Text is the actual line content
	Text string `json:"text"`
}

// LineQuery specifies criteria for retrieving transcript lines.
type LineQuery struct {
	// SessionID to query (required)
	SessionID string
	// AfterSequence returns only lines with sequence > this value (0 = from beginning)
	AfterSequence int64
	// Stream filter ("stdin", "stdout", "stderr", "all"). Default: "all"
	Stream string
	// Limit maximum number of lines to return (0 = no limit)
	Limit int
	// Follow indicates whether to wait for new lines (live streaming)
	Follow bool
}

// TranscriptBackend defines the interface for different storage backends.
type TranscriptBackend interface {
	// GetLines retrieves transcript lines matching the query
	GetLines(ctx context.Context, query LineQuery) ([]TranscriptLine, error)
	// Close releases any resources associated with the backend
	Close() error
}

// TranscriptReader provides a unified interface for reading transcript data
// in both post-mortem and live streaming modes.
type TranscriptReader interface {
	// NextLine returns the next line from the transcript.
	// Returns io.EOF when the transcript is complete and no more lines are available.
	// For live streams, this method blocks until a line is available or the context is cancelled.
	NextLine(ctx context.Context) (*TranscriptLine, error)

	// NextLineAfter returns the next line with sequence number greater than the specified value.
	// This is useful for polling scenarios where clients want to resume from a known position.
	NextLineAfter(ctx context.Context, afterSequence int64) (*TranscriptLine, error)

	// GetLines retrieves multiple lines at once, useful for batch operations.
	GetLines(ctx context.Context, query LineQuery) ([]TranscriptLine, error)

	// SessionID returns the session ID this reader is associated with.
	SessionID() string

	// Close releases any resources associated with the reader.
	Close() error
}

// TranscriptReaderConfig holds configuration options for transcript readers.
type TranscriptReaderConfig struct {
	// BufferSize controls the internal line buffer size for live streams (default: 100)
	BufferSize int
	// FlushInterval controls how often buffered lines are made available (default: 1s)
	FlushInterval time.Duration
	// Stream specifies which stream to read ("stdin", "stdout", "stderr", "all"). Default: "all"
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

// OpenTranscript opens a transcript for reading using the specified backend.
func OpenTranscript(sessionID string, backend TranscriptBackend) (TranscriptReader, error) {
	return OpenTranscriptWithConfig(sessionID, backend, DefaultTranscriptReaderConfig())
}

// OpenTranscriptWithConfig opens a transcript with custom configuration.
func OpenTranscriptWithConfig(sessionID string, backend TranscriptBackend, config TranscriptReaderConfig) (TranscriptReader, error) {
	return &backendTranscriptReader{
		sessionID: sessionID,
		backend:   backend,
		config:    config,
		lastSeq:   0,
	}, nil
}

// OpenTranscriptFile opens a completed transcript file for post-mortem reading.
// This is a convenience function for file-based backends.
func OpenTranscriptFile(path string) (TranscriptReader, error) {
	return OpenTranscriptFileWithConfig(path, DefaultTranscriptReaderConfig())
}

// OpenTranscriptFileWithConfig opens a transcript file with custom configuration.
func OpenTranscriptFileWithConfig(path string, config TranscriptReaderConfig) (TranscriptReader, error) {
	backend, err := NewFileTranscriptBackend(path)
	if err != nil {
		return nil, err
	}

	// Extract session ID from file content or generate one
	sessionID := extractSessionIDFromFile(path)
	if sessionID == "" {
		sessionID = uuid.New().String()
	}

	return &backendTranscriptReader{
		sessionID: sessionID,
		backend:   backend,
		config:    config,
		lastSeq:   0,
	}, nil
} // StreamTranscript creates a live transcript reader that streams output from a running command.
// The reader will continue to provide lines until the command exits or the context is cancelled.
// A new session ID will be generated for this stream.
func StreamTranscript(ctx context.Context, cmd *exec.Cmd) (TranscriptReader, error) {
	return StreamTranscriptWithConfig(ctx, cmd, DefaultTranscriptReaderConfig())
}

// StreamTranscriptWithConfig creates a live transcript reader with custom configuration.
func StreamTranscriptWithConfig(ctx context.Context, cmd *exec.Cmd, config TranscriptReaderConfig) (TranscriptReader, error) {
	sessionID := uuid.New().String()
	return StreamTranscriptWithSession(ctx, sessionID, cmd, config)
}

// StreamTranscriptWithSession creates a live transcript reader with a specific session ID.
func StreamTranscriptWithSession(ctx context.Context, sessionID string, cmd *exec.Cmd, config TranscriptReaderConfig) (TranscriptReader, error) {
	reader := &liveTranscriptReader{
		sessionID: sessionID,
		config:    config,
		linesChan: make(chan *TranscriptLine, config.BufferSize),
		errorChan: make(chan error, 1),
		doneChan:  make(chan struct{}),
		sequence:  0,
	}

	// Start the command and capture its output
	if err := reader.startCapture(ctx, cmd); err != nil {
		return nil, fmt.Errorf("failed to start transcript capture: %w", err)
	}

	return reader, nil
}

// StreamMemoryTranscript creates a live transcript reader from a MemoryTranscript.
// This is useful for testing or when you want to stream from an existing memory transcript.
func StreamMemoryTranscript(ctx context.Context, sessionID string, transcript *MemoryTranscript) TranscriptReader {
	return StreamMemoryTranscriptWithConfig(ctx, sessionID, transcript, DefaultTranscriptReaderConfig())
}

// StreamMemoryTranscriptWithConfig creates a live transcript reader from a MemoryTranscript with custom config.
func StreamMemoryTranscriptWithConfig(ctx context.Context, sessionID string, transcript *MemoryTranscript, config TranscriptReaderConfig) TranscriptReader {
	backend := NewMemoryTranscriptBackend(sessionID, transcript)
	reader := &backendTranscriptReader{
		sessionID: sessionID,
		backend:   backend,
		config:    config,
		lastSeq:   0,
	}

	return reader
}

// backendTranscriptReader implements TranscriptReader using a TranscriptBackend.
type backendTranscriptReader struct {
	sessionID string
	backend   TranscriptBackend
	config    TranscriptReaderConfig
	lastSeq   int64
	mu        sync.Mutex
}

func (r *backendTranscriptReader) SessionID() string {
	return r.sessionID
}

func (r *backendTranscriptReader) NextLine(ctx context.Context) (*TranscriptLine, error) {
	r.mu.Lock()
	lastSeq := r.lastSeq
	r.mu.Unlock()

	return r.NextLineAfter(ctx, lastSeq)
}

func (r *backendTranscriptReader) NextLineAfter(ctx context.Context, afterSequence int64) (*TranscriptLine, error) {
	query := LineQuery{
		SessionID:     r.sessionID,
		AfterSequence: afterSequence,
		Stream:        r.config.Stream,
		Limit:         1,
		Follow:        true,
	}

	lines, err := r.backend.GetLines(ctx, query)
	if err != nil {
		return nil, err
	}

	if len(lines) == 0 {
		return nil, io.EOF
	}

	line := &lines[0]
	r.mu.Lock()
	r.lastSeq = line.Sequence
	r.mu.Unlock()

	return line, nil
}

func (r *backendTranscriptReader) GetLines(ctx context.Context, query LineQuery) ([]TranscriptLine, error) {
	// Override session ID to ensure consistency
	query.SessionID = r.sessionID
	return r.backend.GetLines(ctx, query)
}

func (r *backendTranscriptReader) Close() error {
	return r.backend.Close()
}

// liveTranscriptReader implements TranscriptReader for live command output streaming.
type liveTranscriptReader struct {
	sessionID string
	config    TranscriptReaderConfig
	linesChan chan *TranscriptLine
	errorChan chan error
	doneChan  chan struct{}
	cmd       *exec.Cmd
	sequence  int64
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
		seq := atomic.AddInt64(&r.sequence, 1)
		line := &TranscriptLine{
			SessionID: r.sessionID,
			Sequence:  seq,
			Timestamp: time.Now(),
			Stream:    streamName,
			Text:      scanner.Text(),
		}

		select {
		case <-ctx.Done():
			return
		case r.linesChan <- line:
		}
	}

	if err := scanner.Err(); err != nil {
		select {
		case <-ctx.Done():
		case r.errorChan <- fmt.Errorf("scan error on %s: %w", streamName, err):
		}
	}
}

func (r *liveTranscriptReader) SessionID() string {
	return r.sessionID
}

func (r *liveTranscriptReader) NextLine(ctx context.Context) (*TranscriptLine, error) {
	r.mu.Lock()
	closed := r.closed
	r.mu.Unlock()

	if closed {
		return nil, io.EOF
	}

	select {
	case <-ctx.Done():
		return nil, ctx.Err()
	case line, ok := <-r.linesChan:
		if !ok {
			return nil, io.EOF
		}
		return line, nil
	case err := <-r.errorChan:
		return nil, err
	}
}

func (r *liveTranscriptReader) NextLineAfter(ctx context.Context, afterSequence int64) (*TranscriptLine, error) {
	// For live readers, we need to wait for a line with sequence > afterSequence
	for {
		line, err := r.NextLine(ctx)
		if err != nil {
			return nil, err
		}
		if line.Sequence > afterSequence {
			return line, nil
		}
		// Continue waiting for a line with higher sequence
	}
}

func (r *liveTranscriptReader) GetLines(ctx context.Context, query LineQuery) ([]TranscriptLine, error) {
	// For live readers, collect lines up to the limit
	var lines []TranscriptLine
	limit := query.Limit
	if limit <= 0 {
		limit = 100 // Default limit for safety
	}

	for len(lines) < limit {
		var line *TranscriptLine
		var err error

		if query.AfterSequence > 0 {
			line, err = r.NextLineAfter(ctx, query.AfterSequence+int64(len(lines)))
		} else {
			line, err = r.NextLine(ctx)
		}

		if err == io.EOF {
			break
		}
		if err != nil {
			return nil, err
		}

		// Apply stream filter
		if query.Stream != "all" && line.Stream != query.Stream {
			continue
		}

		lines = append(lines, *line)

		// If not following, stop after collecting available lines
		if !query.Follow {
			// Try to get more without blocking
			select {
			case nextLine, ok := <-r.linesChan:
				if !ok {
					break
				}
				if query.Stream == "all" || nextLine.Stream == query.Stream {
					lines = append(lines, *nextLine)
				}
			default:
				break
			}
		}
	}

	return lines, nil
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

// fileTranscriptBackend implements TranscriptBackend for file-based storage.
type fileTranscriptBackend struct {
	file    *os.File
	scanner *bufio.Scanner
	mu      sync.Mutex
}

// NewFileTranscriptBackend creates a backend for reading transcript files.
func NewFileTranscriptBackend(path string) (TranscriptBackend, error) {
	file, err := os.Open(path)
	if err != nil {
		return nil, fmt.Errorf("failed to open transcript file: %w", err)
	}

	return &fileTranscriptBackend{
		file:    file,
		scanner: bufio.NewScanner(file),
	}, nil
}

func (b *fileTranscriptBackend) GetLines(ctx context.Context, query LineQuery) ([]TranscriptLine, error) {
	b.mu.Lock()
	defer b.mu.Unlock()

	var lines []TranscriptLine
	sequence := int64(1)

	for b.scanner.Scan() {
		select {
		case <-ctx.Done():
			return nil, ctx.Err()
		default:
		}

		rawLine := b.scanner.Text()
		if transcriptLine := b.parseLogLine(rawLine, query.SessionID, sequence); transcriptLine != nil {
			// Apply filters
			if transcriptLine.Sequence <= query.AfterSequence {
				sequence++
				continue
			}
			if query.Stream != "all" && transcriptLine.Stream != query.Stream {
				sequence++
				continue
			}

			lines = append(lines, *transcriptLine)
			sequence++

			if query.Limit > 0 && len(lines) >= query.Limit {
				break
			}
		}
	}

	if err := b.scanner.Err(); err != nil {
		return nil, fmt.Errorf("scan error: %w", err)
	}

	return lines, nil
}

func (b *fileTranscriptBackend) parseLogLine(line, sessionID string, sequence int64) *TranscriptLine {
	// Parse structured log format: time=... level=... msg=io stream=... line=...
	parts := strings.Fields(line)
	var stream, content, timeStr string

	for _, part := range parts {
		if strings.HasPrefix(part, "time=") {
			timeStr = strings.TrimPrefix(part, "time=")
		} else if strings.HasPrefix(part, "stream=") {
			stream = strings.TrimPrefix(part, "stream=")
		} else if strings.HasPrefix(part, "line=") {
			content = strings.TrimPrefix(part, "line=")
			// Handle quoted content
			if strings.HasPrefix(content, `"`) && strings.HasSuffix(content, `"`) {
				content = content[1 : len(content)-1]
			}
		}
	}

	if stream == "" || content == "" {
		return nil
	}

	// Parse timestamp
	timestamp := time.Now()
	if timeStr != "" {
		if parsed, err := time.Parse(time.RFC3339, timeStr); err == nil {
			timestamp = parsed
		}
	}

	return &TranscriptLine{
		SessionID: sessionID,
		Sequence:  sequence,
		Timestamp: timestamp,
		Stream:    stream,
		Text:      content,
	}
}

func (b *fileTranscriptBackend) Close() error {
	if b.file != nil {
		return b.file.Close()
	}
	return nil
}

// memoryTranscriptBackend implements TranscriptBackend for MemoryTranscript.
type memoryTranscriptBackend struct {
	sessionID  string
	transcript *MemoryTranscript
	mu         sync.Mutex
}

// NewMemoryTranscriptBackend creates a backend for MemoryTranscript.
func NewMemoryTranscriptBackend(sessionID string, transcript *MemoryTranscript) TranscriptBackend {
	return &memoryTranscriptBackend{
		sessionID:  sessionID,
		transcript: transcript,
	}
}

func (b *memoryTranscriptBackend) GetLines(ctx context.Context, query LineQuery) ([]TranscriptLine, error) {
	b.mu.Lock()
	defer b.mu.Unlock()

	var lines []TranscriptLine
	sequence := int64(1)

	// Get streams to read based on query
	streams := []string{}
	if query.Stream == "all" {
		streams = []string{"stdin", "stdout", "stderr"}
	} else {
		streams = []string{query.Stream}
	}

	// Collect all lines from all streams and sort by sequence
	type lineWithStream struct {
		line   string
		stream string
		index  int
	}

	var allLines []lineWithStream
	for _, stream := range streams {
		data := b.transcript.GetStreamData(stream)
		if data == nil {
			continue
		}

		streamLines := strings.Split(string(data), "\n")
		for i, line := range streamLines {
			if line == "" && i == len(streamLines)-1 {
				continue // Skip empty line at end
			}
			allLines = append(allLines, lineWithStream{
				line:   line,
				stream: stream,
				index:  i,
			})
		}
	}

	// For simplicity, maintain order within each stream
	// In a real implementation, you'd want proper ordering by timestamp
	for _, lineData := range allLines {
		if sequence <= query.AfterSequence {
			sequence++
			continue
		}

		lines = append(lines, TranscriptLine{
			SessionID: b.sessionID,
			Sequence:  sequence,
			Timestamp: time.Now(), // In real implementation, this would be stored
			Stream:    lineData.stream,
			Text:      lineData.line,
		})
		sequence++

		if query.Limit > 0 && len(lines) >= query.Limit {
			break
		}
	}

	return lines, nil
}

func (b *memoryTranscriptBackend) Close() error {
	return nil
}

// Helper function to extract session ID from file content
func extractSessionIDFromFile(path string) string {
	// For now, just return empty string - in real implementation
	// you might parse the file header or use a naming convention
	return ""
}
