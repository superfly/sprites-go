package lib

import (
	"io"
	"sync"
	"sync/atomic"
)

// MultiPipe is an io.Writer that multiplexes written data to multiple readers.
// Writes never block - if a reader's buffer is full, data is dropped for that reader.
type MultiPipe struct {
	writeCh       chan writeOp
	subscribeCh   chan subscribeOp
	unsubscribeCh chan int64
	closeCh       chan struct{}
	bufferSize    int
	closed        atomic.Bool
	wg            sync.WaitGroup
}

type writeOp struct {
	data []byte
	done chan int
}

type subscribeOp struct {
	sub  *subscriber
	done chan struct{}
}

// subscriber represents a single reader
type subscriber struct {
	id     int64
	ch     chan []byte
	closed atomic.Bool
}

var nextID atomic.Int64

// NewMultiPipe creates a new MultiPipe with the specified buffer size per reader
func NewMultiPipe(bufferSize int) *MultiPipe {
	if bufferSize <= 0 {
		bufferSize = 1024 // Default buffer size
	}

	mp := &MultiPipe{
		writeCh:       make(chan writeOp),
		subscribeCh:   make(chan subscribeOp),
		unsubscribeCh: make(chan int64),
		closeCh:       make(chan struct{}),
		bufferSize:    bufferSize,
	}

	mp.wg.Add(1)
	go mp.run()

	return mp
}

// run is the main goroutine that manages all subscribers
func (mp *MultiPipe) run() {
	defer mp.wg.Done()

	subscribers := make(map[int64]*subscriber)

	for {
		select {
		case op := <-mp.writeCh:
			// Broadcast to all subscribers
			for _, sub := range subscribers {
				if sub.closed.Load() {
					continue
				}

				// Non-blocking send
				select {
				case sub.ch <- op.data:
				default:
					// Buffer full, drop
				}
			}
			op.done <- len(op.data)

		case op := <-mp.subscribeCh:
			subscribers[op.sub.id] = op.sub
			close(op.done)

		case id := <-mp.unsubscribeCh:
			delete(subscribers, id)

		case <-mp.closeCh:
			// Close all subscriber channels
			for _, sub := range subscribers {
				if !sub.closed.CompareAndSwap(false, true) {
					continue
				}
				close(sub.ch)
			}
			return
		}
	}
}

// Write implements io.Writer. It never blocks - data is dropped if a reader's buffer is full.
func (mp *MultiPipe) Write(p []byte) (n int, err error) {
	if mp.closed.Load() {
		return 0, io.ErrClosedPipe
	}

	// Make a copy since we're passing to goroutines
	data := make([]byte, len(p))
	copy(data, p)

	done := make(chan int, 1)
	select {
	case mp.writeCh <- writeOp{data: data, done: done}:
		return <-done, nil
	case <-mp.closeCh:
		return 0, io.ErrClosedPipe
	}
}

// NewReader creates a new reader that will receive all data written to the MultiPipe.
// The returned reader can be closed to unsubscribe.
func (mp *MultiPipe) NewReader() io.ReadCloser {
	if mp.closed.Load() {
		return &closedReader{}
	}

	sub := &subscriber{
		id: nextID.Add(1),
		ch: make(chan []byte, mp.bufferSize),
	}

	done := make(chan struct{})
	select {
	case mp.subscribeCh <- subscribeOp{sub: sub, done: done}:
		<-done
		return &reader{
			multipipe: mp,
			sub:       sub,
		}
	case <-mp.closeCh:
		return &closedReader{}
	}
}

// Close closes the MultiPipe and all active readers
func (mp *MultiPipe) Close() error {
	if !mp.closed.CompareAndSwap(false, true) {
		return nil // Already closed
	}

	close(mp.closeCh)
	mp.wg.Wait()

	return nil
}

// reader implements io.ReadCloser for a single subscriber
type reader struct {
	multipipe *MultiPipe
	sub       *subscriber
	buffer    []byte // Partial read buffer
}

// Read implements io.Reader
func (r *reader) Read(p []byte) (n int, err error) {
	// If we have buffered data from a previous read, use that first
	if len(r.buffer) > 0 {
		n = copy(p, r.buffer)
		r.buffer = r.buffer[n:]
		return n, nil
	}

	// Read from channel
	data, ok := <-r.sub.ch
	if !ok {
		return 0, io.EOF
	}

	// Copy as much as fits in p
	n = copy(p, data)

	// Buffer any remainder
	if n < len(data) {
		r.buffer = data[n:]
	}

	return n, nil
}

// Close implements io.Closer
func (r *reader) Close() error {
	if !r.sub.closed.CompareAndSwap(false, true) {
		return nil // Already closed
	}

	// Send unsubscribe message
	select {
	case r.multipipe.unsubscribeCh <- r.sub.id:
	case <-r.multipipe.closeCh:
		// MultiPipe is closed
	}

	// Close the channel
	close(r.sub.ch)

	return nil
}

// closedReader is returned when trying to create a reader on a closed MultiPipe
type closedReader struct{}

func (cr *closedReader) Read(p []byte) (n int, err error) {
	return 0, io.EOF
}

func (cr *closedReader) Close() error {
	return nil
}
