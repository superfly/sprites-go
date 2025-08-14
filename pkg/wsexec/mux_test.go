package wsexec

import (
	"bytes"
	"io"
	"sync"
	"testing"
)

func TestMuxBasicWriteToAndReaders(t *testing.T) {
	m := NewMux()
	wOut := m.Writer(StreamStdout)
	wErr := m.Writer(StreamStderr)

	// Start a transport that captures multiplexed bytes
	var muxed bytes.Buffer
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		_, err := m.WriteTo(&muxed)
		if err != nil && err != io.EOF {
			t.Errorf("WriteTo error: %v", err)
		}
	}()

	// Emit data on both streams
	_, _ = wOut.Write([]byte("hello"))
	_, _ = wErr.Write([]byte("oops"))
	m.CloseOutput()
	wg.Wait()

	// Now feed back through ReadFrom and read from per-stream readers
	m2 := NewMux()
	rOut := m2.Reader(StreamStdout)
	rErr := m2.Reader(StreamStderr)
	go func() { _, _ = m2.ReadFrom(bytes.NewReader(muxed.Bytes())) }()

	buf := make([]byte, 5)
	n, err := io.ReadFull(rOut, buf)
	if err != nil || n != 5 || string(buf) != "hello" {
		t.Fatalf("stdout got %q err=%v", string(buf[:n]), err)
	}
	n, err = io.ReadFull(rErr, buf[:4])
	if err != nil || n != 4 || string(buf[:4]) != "oops" {
		t.Fatalf("stderr got %q err=%v", string(buf[:n]), err)
	}
}

func TestMuxReaderFromLargePayloads(t *testing.T) {
	m := NewMux()
	w := m.Writer(StreamStdout)
	payload := bytes.Repeat([]byte{'x'}, 100000)
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		_, _ = w.ReadFrom(bytes.NewReader(payload))
		m.CloseOutput()
	}()
	var out bytes.Buffer
	_, err := m.WriteTo(&out)
	if err != nil && err != io.EOF {
		t.Fatalf("WriteTo: %v", err)
	}
	wg.Wait()

	m2 := NewMux()
	go func() { _, _ = m2.ReadFrom(bytes.NewReader(out.Bytes())) }()
	r := m2.Reader(StreamStdout)
	var collected bytes.Buffer
	if _, err := io.Copy(&collected, r); err != nil && err != io.EOF {
		t.Fatalf("copy: %v", err)
	}
	if collected.Len() != len(payload) {
		t.Fatalf("size mismatch: %d != %d", collected.Len(), len(payload))
	}
	if !bytes.Equal(collected.Bytes(), payload) {
		t.Fatalf("payload mismatch")
	}
}

func TestMuxPartialWritesCombine(t *testing.T) {
	m := NewMux()
	w := m.Writer(StreamStdout)
	var out bytes.Buffer
	var wg sync.WaitGroup
	wg.Add(1)
	go func() {
		defer wg.Done()
		_, _ = m.WriteTo(&out)
	}()
	// Write small chunks
	_, _ = w.Write([]byte("a"))
	_, _ = w.Write([]byte("bcd"))
	m.CloseOutput()
	wg.Wait()

	m2 := NewMux()
	go func() { _, _ = m2.ReadFrom(bytes.NewReader(out.Bytes())) }()
	r := m2.Reader(StreamStdout)
	buf := make([]byte, 4)
	n, err := io.ReadFull(r, buf)
	if err != nil || n != 4 || string(buf) != "abcd" {
		t.Fatalf("got %q err=%v", string(buf[:n]), err)
	}
}

func TestMuxMultipleStreamsOrdering(t *testing.T) {
	m := NewMux()
	w1 := m.Writer(StreamStdout)
	w2 := m.Writer(StreamStderr)
	var out bytes.Buffer
	var wg sync.WaitGroup
	wg.Add(1)
	go func() { defer wg.Done(); _, _ = m.WriteTo(&out) }()
	_, _ = w1.Write([]byte("A"))
	_, _ = w2.Write([]byte("B"))
	_, _ = w1.Write([]byte("C"))
	m.CloseOutput()
	wg.Wait()

	m2 := NewMux()
	go func() { _, _ = m2.ReadFrom(bytes.NewReader(out.Bytes())) }()
	r1 := m2.Reader(StreamStdout)
	r2 := m2.Reader(StreamStderr)
	buf := make([]byte, 1)
	n, _ := io.ReadFull(r1, buf)
	if string(buf[:n]) != "A" {
		t.Fatalf("r1 first %q", string(buf[:n]))
	}
	n, _ = io.ReadFull(r2, buf)
	if string(buf[:n]) != "B" {
		t.Fatalf("r2 first %q", string(buf[:n]))
	}
	n, _ = io.ReadFull(r1, buf)
	if string(buf[:n]) != "C" {
		t.Fatalf("r1 second %q", string(buf[:n]))
	}
}
