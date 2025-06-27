package handlers

import (
	"bytes"
	"context"
	"database/sql"
	"fmt"
	"io"
	"strings"
	"sync"
	"sync/atomic"
	"time"

	_ "github.com/mattn/go-sqlite3"
)

const (
	batchSize      = 100
	flushInterval  = time.Second
	logChannelSize = 1000
)

type logLine struct {
	stream string
	text   string
	id     int64
}

type sqliteWriter struct {
	c      *SQLiteLogCollector
	stream string
	buf    bytes.Buffer
}

func (w *sqliteWriter) Write(p []byte) (int, error) {
	w.buf.Write(p)
	for {
		line, err := w.buf.ReadString('\n')
		if err != nil {
			break
		}
		w.c.insert(strings.TrimSuffix(line, "\n"), w.stream)
	}
	return len(p), nil
}

type SQLiteLogCollector struct {
	db       *sql.DB
	ts       int64
	seq      atomic.Int64
	counters map[string]int
	writers  []*sqliteWriter

	linesCh chan logLine
	wg      sync.WaitGroup
	cancel  context.CancelFunc

	mu     sync.Mutex
	closed bool
}

func NewSQLiteLogCollector(dsn string) (*SQLiteLogCollector, error) {
	db, err := sql.Open("sqlite3", dsn)
	if err != nil {
		return nil, fmt.Errorf("open db: %w", err)
	}

	pragmas := []string{
		"PRAGMA journal_mode = WAL",
		"PRAGMA synchronous = NORMAL",
		"PRAGMA temp_store = MEMORY",
		"PRAGMA mmap_size = 1073741824",
		"PRAGMA wal_autocheckpoint = 500",
	}
	for _, p := range pragmas {
		if _, err := db.Exec(p); err != nil {
			db.Close()
			return nil, fmt.Errorf("pragma %q: %w", p, err)
		}
	}

	createTable := `CREATE TABLE IF NOT EXISTS session_logs (
       session_ts INTEGER,
       stream     TEXT,
       line_num   INTEGER,
       line_id    INTEGER,
       text       TEXT
    )`
	if _, err = db.Exec(createTable); err != nil {
		db.Close()
		return nil, fmt.Errorf("create table: %w", err)
	}

	createIndex := `CREATE INDEX IF NOT EXISTS idx_session_line ON session_logs(session_ts, line_id)`
	if _, err = db.Exec(createIndex); err != nil {
		db.Close()
		return nil, fmt.Errorf("create index: %w", err)
	}

	ctx, cancel := context.WithCancel(context.Background())

	s := &SQLiteLogCollector{
		db:       db,
		ts:       time.Now().UnixNano(),
		counters: make(map[string]int),
		linesCh:  make(chan logLine, logChannelSize),
		cancel:   cancel,
	}

	s.wg.Add(1)
	go s.batchProcessor(ctx)

	return s, nil
}

func (s *SQLiteLogCollector) closedp() bool {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.closed
}

func (s *SQLiteLogCollector) insert(line, stream string) {
	if s.closedp() {
		return
	}

	id := s.seq.Add(1)
	s.linesCh <- logLine{stream: stream, text: line, id: id}
}

func (s *SQLiteLogCollector) Stream(name string) io.Writer {
	s.mu.Lock()
	defer s.mu.Unlock()

	if s.closed {
		return io.Discard
	}

	w := &sqliteWriter{c: s, stream: name}
	s.writers = append(s.writers, w)
	return w
}

func (s *SQLiteLogCollector) Close() error {
	if s.closedp() {
		return nil
	}

	s.mu.Lock()
	s.closed = true
	writers := s.writers
	s.writers = nil
	s.mu.Unlock()

	for _, w := range writers {
		w.Write([]byte("\n"))
	}

	s.cancel()
	s.wg.Wait()

	if s.db == nil {
		return nil
	}

	return s.db.Close()
}

func (s *SQLiteLogCollector) batchProcessor(ctx context.Context) {
	defer s.wg.Done()

	batch := make([]logLine, 0, batchSize)
	ticker := time.NewTicker(flushInterval)
	defer ticker.Stop()

	for {
		select {
		case <-ctx.Done():
			close(s.linesCh)
			for line := range s.linesCh {
				batch = append(batch, line)
			}
			if len(batch) > 0 {
				s.flushBatch(batch)
			}
			return
		case line := <-s.linesCh:
			batch = append(batch, line)
			if len(batch) >= batchSize {
				s.flushBatch(batch)
				batch = make([]logLine, 0, batchSize)
			}
		case <-ticker.C:
			if len(batch) > 0 {
				s.flushBatch(batch)
				batch = make([]logLine, 0, batchSize)
			}
		}
	}
}

func (s *SQLiteLogCollector) flushBatch(batch []logLine) error {
	type numberedLine struct {
		stream string
		text   string
		num    int
		id     int64
	}
	numberedBatch := make([]numberedLine, len(batch))

	s.mu.Lock()
	for i, line := range batch {
		s.counters[line.stream]++
		numberedBatch[i] = numberedLine{
			stream: line.stream,
			text:   line.text,
			num:    s.counters[line.stream],
			id:     line.id,
		}
	}
	s.mu.Unlock()

	tx, err := s.db.Begin()
	if err != nil {
		return fmt.Errorf("begin transaction: %w", err)
	}
	defer tx.Rollback()

	stmt, err := tx.Prepare(
		`INSERT INTO session_logs(
                        session_ts,
                        stream,
                        line_num,
                        line_id,
                        text,
                ) VALUES(?,?,?,?,?)`,
	)
	if err != nil {
		return fmt.Errorf("prepare statement: %w", err)
	}
	defer stmt.Close()

	for _, line := range numberedBatch {
		if _, err := stmt.Exec(
			s.ts,
			line.stream,
			line.num,
			line.id,
			line.text,
		); err != nil {
			return fmt.Errorf(
				"exec statement for stream %q: %w",
				line.stream,
				err,
			)
		}
	}

	return tx.Commit()
}
