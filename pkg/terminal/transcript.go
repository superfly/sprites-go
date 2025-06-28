package terminal

import (
	"bytes"
	"fmt"
	"io"
	"log/slog"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"time"
)

// TranscriptCollector defines the interface for recording session I/O.
type TranscriptCollector interface {
	// StreamWriter returns a writer for the named stream (e.g., "stdin", "stdout", "stderr").
	StreamWriter(name string) io.Writer

	// Close closes the transcript collector and releases any resources.
	Close() error
}

// noopTranscript is a TranscriptCollector that discards all output.
type noopTranscript struct{}

func (n *noopTranscript) StreamWriter(name string) io.Writer {
	return io.Discard
}

func (n *noopTranscript) Close() error {
	return nil
}

// MemoryTranscript collects transcript data in memory.
type MemoryTranscript struct {
	mu      sync.Mutex
	streams map[string]*bytes.Buffer
}

// NewMemoryTranscript creates a new in-memory transcript collector.
func NewMemoryTranscript() *MemoryTranscript {
	return &MemoryTranscript{
		streams: make(map[string]*bytes.Buffer),
	}
}

func (m *MemoryTranscript) StreamWriter(name string) io.Writer {
	m.mu.Lock()
	defer m.mu.Unlock()

	if _, exists := m.streams[name]; !exists {
		m.streams[name] = &bytes.Buffer{}
	}
	return &memoryStreamWriter{transcript: m, streamName: name}
}

func (m *MemoryTranscript) Close() error {
	return nil
}

// GetStreamData returns the collected data for a specific stream.
func (m *MemoryTranscript) GetStreamData(name string) []byte {
	m.mu.Lock()
	defer m.mu.Unlock()

	if buf, exists := m.streams[name]; exists {
		return buf.Bytes()
	}
	return nil
}

// GetAllStreams returns all collected stream data.
func (m *MemoryTranscript) GetAllStreams() map[string][]byte {
	m.mu.Lock()
	defer m.mu.Unlock()

	result := make(map[string][]byte)
	for name, buf := range m.streams {
		result[name] = buf.Bytes()
	}
	return result
}

type memoryStreamWriter struct {
	transcript *MemoryTranscript
	streamName string
}

func (w *memoryStreamWriter) Write(p []byte) (n int, err error) {
	w.transcript.mu.Lock()
	defer w.transcript.mu.Unlock()

	if buf, exists := w.transcript.streams[w.streamName]; exists {
		return buf.Write(p)
	}
	return len(p), nil
}

// FileTranscript collects transcript data to a file.
type FileTranscript struct {
	file    *os.File
	logger  *slog.Logger
	streams []*lineWriter
	mu      sync.Mutex
}

// NewFileTranscript creates a new file-based transcript collector.
func NewFileTranscript(basePath string) (*FileTranscript, error) {
	// Generate unique filename
	ext := filepath.Ext(basePath)
	name := strings.TrimSuffix(basePath, ext)
	path := fmt.Sprintf("%s-%d%s", name, time.Now().UnixNano(), ext)

	f, err := os.OpenFile(path, os.O_CREATE|os.O_WRONLY|os.O_APPEND, 0644)
	if err != nil {
		return nil, fmt.Errorf("failed to create transcript file: %w", err)
	}

	return &FileTranscript{
		file:   f,
		logger: slog.New(slog.NewTextHandler(f, nil)),
	}, nil
}

func (f *FileTranscript) StreamWriter(name string) io.Writer {
	f.mu.Lock()
	defer f.mu.Unlock()

	writer := newLineWriter(name, f.logger)
	f.streams = append(f.streams, writer)
	return writer
}

func (f *FileTranscript) Close() error {
	f.mu.Lock()
	defer f.mu.Unlock()

	// Close all stream writers
	for _, stream := range f.streams {
		stream.Close()
	}

	// Close the file
	if f.file != nil {
		return f.file.Close()
	}
	return nil
}

// lineWriter buffers writes and logs complete lines.
type lineWriter struct {
	logger *slog.Logger
	stream string
	mu     sync.Mutex
	buf    bytes.Buffer
}

func newLineWriter(name string, logger *slog.Logger) *lineWriter {
	return &lineWriter{logger: logger, stream: name}
}

func (l *lineWriter) Write(p []byte) (int, error) {
	if l == nil {
		return len(p), nil
	}

	l.mu.Lock()
	defer l.mu.Unlock()

	n := len(p)
	l.buf.Write(p)

	// Process complete lines
	for {
		line, err := l.buf.ReadString('\n')
		if err != nil {
			// Put the incomplete line back
			if line != "" {
				remaining := l.buf.Bytes()
				l.buf.Reset()
				l.buf.WriteString(line)
				l.buf.Write(remaining)
			}
			break
		}

		// Log the complete line (without newline)
		line = strings.TrimSuffix(line, "\n")
		l.logger.Info("io", "stream", l.stream, "line", line)
	}

	return n, nil
}

func (l *lineWriter) Close() {
	if l == nil {
		return
	}

	l.mu.Lock()
	defer l.mu.Unlock()

	// Log any remaining buffered content
	if l.logger != nil && l.buf.Len() > 0 {
		line := strings.TrimRight(l.buf.String(), "\n")
		l.logger.Info("io", "stream", l.stream, "line", line)
	}
	l.buf.Reset()
}
