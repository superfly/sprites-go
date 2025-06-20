package lib

import (
	"bytes"
	"io"
	"sync"
	"testing"
	"time"
)

func TestBasicWriteRead(t *testing.T) {
	mp := NewMultiPipe(10)
	defer mp.Close()

	// Create a reader
	reader := mp.NewReader()
	defer reader.Close()

	// Write some data
	testData := []byte("hello world")
	n, err := mp.Write(testData)
	if err != nil {
		t.Fatalf("Write failed: %v", err)
	}
	if n != len(testData) {
		t.Fatalf("Expected to write %d bytes, wrote %d", len(testData), n)
	}

	// Read the data
	buf := make([]byte, 100)
	n, err = reader.Read(buf)
	if err != nil {
		t.Fatalf("Read failed: %v", err)
	}
	if n != len(testData) {
		t.Fatalf("Expected to read %d bytes, read %d", len(testData), n)
	}
	if !bytes.Equal(buf[:n], testData) {
		t.Fatalf("Expected %q, got %q", testData, buf[:n])
	}
}

func TestMultipleReaders(t *testing.T) {
	mp := NewMultiPipe(10)
	defer mp.Close()

	// Create multiple readers
	readers := make([]io.ReadCloser, 3)
	for i := range readers {
		readers[i] = mp.NewReader()
		defer readers[i].Close()
	}

	// Write data
	testData := []byte("broadcast message")
	mp.Write(testData)

	// Each reader should receive the data
	for i, reader := range readers {
		buf := make([]byte, 100)
		n, err := reader.Read(buf)
		if err != nil {
			t.Fatalf("Reader %d: Read failed: %v", i, err)
		}
		if !bytes.Equal(buf[:n], testData) {
			t.Fatalf("Reader %d: Expected %q, got %q", i, testData, buf[:n])
		}
	}
}

func TestNonBlockingWrite(t *testing.T) {
	mp := NewMultiPipe(1) // Small buffer
	defer mp.Close()

	reader := mp.NewReader()
	defer reader.Close()

	// Fill the buffer
	mp.Write([]byte("1"))
	mp.Write([]byte("2"))

	// This write should not block, even though buffer is full
	done := make(chan bool)
	go func() {
		mp.Write([]byte("3")) // This will be dropped
		done <- true
	}()

	select {
	case <-done:
		// Good, write didn't block
	case <-time.After(100 * time.Millisecond):
		t.Fatal("Write blocked when it shouldn't")
	}

	// Read what's available
	buf := make([]byte, 1)
	n, _ := reader.Read(buf)
	if n != 1 || buf[0] != '1' {
		t.Fatalf("Expected to read '1', got %q", buf[:n])
	}
}

func TestReaderClose(t *testing.T) {
	mp := NewMultiPipe(10)
	defer mp.Close()

	reader1 := mp.NewReader()
	reader2 := mp.NewReader()

	// Close reader1
	reader1.Close()

	// Write should still work for reader2
	testData := []byte("still working")
	mp.Write(testData)

	buf := make([]byte, 100)
	n, err := reader2.Read(buf)
	if err != nil {
		t.Fatalf("Read failed: %v", err)
	}
	if !bytes.Equal(buf[:n], testData) {
		t.Fatalf("Expected %q, got %q", testData, buf[:n])
	}

	// Reading from closed reader should return EOF
	_, err = reader1.Read(buf)
	if err != io.EOF {
		t.Fatalf("Expected EOF from closed reader, got %v", err)
	}

	reader2.Close()
}

func TestMultiPipeClose(t *testing.T) {
	mp := NewMultiPipe(10)
	reader := mp.NewReader()

	mp.Close()

	// Write to closed multipipe should fail
	_, err := mp.Write([]byte("test"))
	if err != io.ErrClosedPipe {
		t.Fatalf("Expected ErrClosedPipe, got %v", err)
	}

	// Creating new reader on closed multipipe should return closed reader
	newReader := mp.NewReader()
	_, err = newReader.Read(make([]byte, 10))
	if err != io.EOF {
		t.Fatalf("Expected EOF from reader on closed multipipe, got %v", err)
	}

	// Existing reader should get EOF
	_, err = reader.Read(make([]byte, 10))
	if err != io.EOF {
		t.Fatalf("Expected EOF from reader after multipipe close, got %v", err)
	}
}

func TestPartialReads(t *testing.T) {
	mp := NewMultiPipe(10)
	defer mp.Close()

	reader := mp.NewReader()
	defer reader.Close()

	// Write a large message
	testData := []byte("this is a longer message that might not fit in one read")
	mp.Write(testData)

	// Read in small chunks
	var result []byte
	smallBuf := make([]byte, 10)
	for {
		n, err := reader.Read(smallBuf)
		if err == io.EOF {
			break
		}
		if err != nil {
			t.Fatalf("Read failed: %v", err)
		}
		result = append(result, smallBuf[:n]...)
		if len(result) >= len(testData) {
			break
		}
	}

	if !bytes.Equal(result, testData) {
		t.Fatalf("Expected %q, got %q", testData, result)
	}
}

func TestConcurrentWritesReads(t *testing.T) {
	mp := NewMultiPipe(100)
	defer mp.Close()

	const numWriters = 5
	const numReaders = 3
	const messagesPerWriter = 100

	var wg sync.WaitGroup

	// Start readers
	readers := make([]io.ReadCloser, numReaders)
	readCounts := make([]int, numReaders)
	for i := 0; i < numReaders; i++ {
		readers[i] = mp.NewReader()
		readerIdx := i
		wg.Add(1)
		go func() {
			defer wg.Done()
			defer readers[readerIdx].Close()
			buf := make([]byte, 100)
			for {
				_, err := readers[readerIdx].Read(buf)
				if err == io.EOF {
					break
				}
				if err != nil {
					t.Errorf("Reader %d: Read failed: %v", readerIdx, err)
					break
				}
				readCounts[readerIdx]++
			}
		}()
	}

	// Give readers time to start
	time.Sleep(10 * time.Millisecond)

	// Start writers
	for i := 0; i < numWriters; i++ {
		writerIdx := i
		wg.Add(1)
		go func() {
			defer wg.Done()
			for j := 0; j < messagesPerWriter; j++ {
				msg := []byte(string(rune('A'+writerIdx)) + string(rune('0'+j%10)))
				mp.Write(msg)
			}
		}()
	}

	// Let everything run
	time.Sleep(100 * time.Millisecond)

	// Close multipipe to signal readers to stop
	mp.Close()

	// Wait for all goroutines
	wg.Wait()

	// Each reader should have received some messages
	for i, count := range readCounts {
		if count == 0 {
			t.Errorf("Reader %d received no messages", i)
		}
		t.Logf("Reader %d received %d messages", i, count)
	}
}

func TestWithMultiWriter(t *testing.T) {
	mp := NewMultiPipe(10)
	defer mp.Close()

	reader := mp.NewReader()
	defer reader.Close()

	// Use with io.MultiWriter
	var buf bytes.Buffer
	mw := io.MultiWriter(&buf, mp)

	// Write through MultiWriter
	testData := []byte("through multiwriter")
	n, err := mw.Write(testData)
	if err != nil {
		t.Fatalf("MultiWriter write failed: %v", err)
	}
	if n != len(testData) {
		t.Fatalf("Expected to write %d bytes, wrote %d", len(testData), n)
	}

	// Check buffer got the data
	if !bytes.Equal(buf.Bytes(), testData) {
		t.Fatalf("Buffer: Expected %q, got %q", testData, buf.Bytes())
	}

	// Check reader got the data
	readBuf := make([]byte, 100)
	n, err = reader.Read(readBuf)
	if err != nil {
		t.Fatalf("Read failed: %v", err)
	}
	if !bytes.Equal(readBuf[:n], testData) {
		t.Fatalf("Reader: Expected %q, got %q", testData, readBuf[:n])
	}
}
