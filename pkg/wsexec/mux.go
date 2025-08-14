package wsexec

import (
	"encoding/binary"
	"io"
)

type StreamID byte

const (
	StreamStdin    StreamID = 0x00
	StreamStdout   StreamID = 0x01
	StreamStderr   StreamID = 0x02
	StreamExit     StreamID = 0x03
	StreamStdinEOF StreamID = 0x04
)

type frame struct {
	id   StreamID
	data []byte
}

type Mux struct {
	// outgoing frames (from stream writers) serialized here
	out chan frame
	// incoming per-stream payload channels
	in [256]chan []byte

	// state for Reader of multiplexed stream
	outHeader  [5]byte
	outHdrIdx  int
	outPayload []byte
}

func NewMux() *Mux {
	m := &Mux{
		out: make(chan frame),
	}
	for i := range m.in {
		m.in[i] = make(chan []byte)
	}
	return m
}

// Writer returns an io.Writer and io.ReaderFrom for the given stream ID.
func (m *Mux) Writer(id StreamID) *StreamWriter {
	return &StreamWriter{id: id, out: m.out}
}

// Reader returns an io.Reader for the given stream ID.
func (m *Mux) Reader(id StreamID) io.Reader { return &StreamReader{ch: m.in[id]} }

// StreamWriter multiplexes writes for a specific stream ID.
type StreamWriter struct {
	id  StreamID
	out chan frame
}

func (w *StreamWriter) Write(p []byte) (int, error) {
	// forward as a single frame; backpressure via unbuffered channel
	payload := make([]byte, len(p))
	copy(payload, p)
	w.out <- frame{id: w.id, data: payload}
	return len(p), nil
}

// ReaderFrom copies from r and emits frames chunk-by-chunk.
func (w *StreamWriter) ReadFrom(r io.Reader) (n int64, err error) {
	buf := make([]byte, 32*1024)
	for {
		k, rerr := r.Read(buf)
		if k > 0 {
			payload := make([]byte, k)
			copy(payload, buf[:k])
			w.out <- frame{id: w.id, data: payload}
			n += int64(k)
		}
		if rerr != nil {
			if rerr == io.EOF {
				return n, nil
			}
			return n, rerr
		}
	}
}

// StreamReader demultiplexes payloads for a specific stream ID.
type StreamReader struct {
	ch       chan []byte
	leftover []byte
}

func (r *StreamReader) Read(p []byte) (int, error) {
	if len(r.leftover) == 0 {
		payload, ok := <-r.ch
		if !ok {
			return 0, io.EOF
		}
		r.leftover = payload
	}
	n := copy(p, r.leftover)
	r.leftover = r.leftover[n:]
	return n, nil
}

// io.Reader for multiplexed outgoing stream.
func (m *Mux) Read(p []byte) (int, error) {
	for {
		// send header then payload without buffering beyond current frame
		if m.outHdrIdx < len(m.outHeader) && len(m.outPayload) > 0 {
			n := copy(p, m.outHeader[m.outHdrIdx:])
			m.outHdrIdx += n
			if n > 0 {
				return n, nil
			}
		}
		if m.outHdrIdx >= len(m.outHeader) && len(m.outPayload) > 0 {
			n := copy(p, m.outPayload)
			m.outPayload = m.outPayload[n:]
			if n > 0 {
				return n, nil
			}
		}
		// need a new frame
		f, ok := <-m.out
		if !ok {
			return 0, io.EOF
		}
		m.outHeader[0] = byte(f.id)
		binary.BigEndian.PutUint32(m.outHeader[1:], uint32(len(f.data)))
		m.outHdrIdx = 0
		m.outPayload = f.data
	}
}

// io.WriterTo for multiplexed outgoing stream.
func (m *Mux) WriteTo(w io.Writer) (int64, error) {
	var total int64
	for f := range m.out {
		var hdr [5]byte
		hdr[0] = byte(f.id)
		binary.BigEndian.PutUint32(hdr[1:], uint32(len(f.data)))
		if err := writeAll(w, hdr[:]); err != nil {
			return total, err
		}
		if err := writeAll(w, f.data); err != nil {
			return total, err
		}
		total += int64(5 + len(f.data))
	}
	return total, nil
}

func writeAll(w io.Writer, b []byte) error {
	for len(b) > 0 {
		n, err := w.Write(b)
		if err != nil {
			return err
		}
		b = b[n:]
	}
	return nil
}

// CloseOutput closes the outgoing frame channel. Call once after all writers are finished.
func (m *Mux) CloseOutput() { close(m.out) }

// io.Writer for multiplexed incoming stream (expects complete frames within p).
// Format: 1 byte stream ID, 4 bytes BE length, then payload.
// If p ends mid-frame, returns bytes consumed up to last complete frame.
func (m *Mux) Write(p []byte) (int, error) {
	var off int
	for {
		if len(p[off:]) < 5 {
			return off, nil
		}
		id := p[off]
		ln := int(binary.BigEndian.Uint32(p[off+1:]))
		if len(p[off+5:]) < ln {
			return off, nil
		}
		payload := make([]byte, ln)
		copy(payload, p[off+5:off+5+ln])
		m.in[id] <- payload
		off += 5 + ln
		if off >= len(p) {
			return off, nil
		}
	}
}

// io.ReaderFrom for multiplexed incoming stream. Reads exact frames from r.
func (m *Mux) ReadFrom(r io.Reader) (int64, error) {
	var total int64
	var hdr [5]byte
	for {
		if _, err := io.ReadFull(r, hdr[:]); err != nil {
			for i := range m.in {
				close(m.in[i])
			}
			return total, err
		}
		id := hdr[0]
		ln := int(binary.BigEndian.Uint32(hdr[1:]))
		payload := make([]byte, ln)
		if _, err := io.ReadFull(r, payload); err != nil {
			for i := range m.in {
				close(m.in[i])
			}
			return total, err
		}
		m.in[id] <- payload
		total += int64(5 + ln)
	}
}

// Helper: a zero-copy reader over a byte slice without allocation.
type bytesReader []byte

func (b bytesReader) Read(p []byte) (int, error) {
	n := copy(p, b)
	if n < len(b) {
		return n, nil
	}
	return n, io.EOF
}
