package runner

import (
	"io"
	"sync"
)

// stream identifiers for non-TTY multiplexed frames (kept internal to runner)
const (
	streamStdout byte = 0x01
	streamStderr byte = 0x02
	streamExit   byte = 0x03
)

// MultiplexedWriter serializes writes and prefixes payloads with a stream ID.
// It is intended for non-TTY mode where stdout, stderr and exit are carried
// over a single binary channel.
type MultiplexedWriter struct {
	base io.Writer
	mu   sync.Mutex
}

// NewMultiplexedWriter constructs a new MultiplexedWriter wrapping the given writer.
func NewMultiplexedWriter(base io.Writer) *MultiplexedWriter {
	return &MultiplexedWriter{base: base}
}

// stdoutWriter returns an io.Writer that writes stdout frames.
func (m *MultiplexedWriter) stdoutWriter() io.Writer { return &streamWriter{m: m, id: streamStdout} }

// stderrWriter returns an io.Writer that writes stderr frames.
func (m *MultiplexedWriter) stderrWriter() io.Writer { return &streamWriter{m: m, id: streamStderr} }

// StdoutWriter exposes a writer for stdout frames.
func (m *MultiplexedWriter) StdoutWriter() io.Writer { return m.stdoutWriter() }

// StderrWriter exposes a writer for stderr frames.
func (m *MultiplexedWriter) StderrWriter() io.Writer { return m.stderrWriter() }

// WriteExit writes an exit code frame synchronously.
func (m *MultiplexedWriter) WriteExit(code int) error {
	if code < 0 || code > 255 {
		code = 255
	}
	m.mu.Lock()
	defer m.mu.Unlock()
	buf := []byte{streamExit, byte(code)}
	_, err := m.base.Write(buf)
	return err
}

// streamWriter prefixes writes with a specific stream ID.
type streamWriter struct {
	m  *MultiplexedWriter
	id byte
}

func (w *streamWriter) Write(p []byte) (int, error) {
	w.m.mu.Lock()
	defer w.m.mu.Unlock()
	buf := make([]byte, len(p)+1)
	buf[0] = w.id
	copy(buf[1:], p)
	n, err := w.m.base.Write(buf)
	if n <= 0 {
		return 0, err
	}
	// Adjust reported bytes to exclude the stream ID prefix
	written := n - 1
	if written < 0 {
		written = 0
	}
	return written, err
}

