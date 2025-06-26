package handlers

import (
	"bytes"
	"database/sql"
	"io"
	"strings"
	"sync"
	"time"

	_ "github.com/mattn/go-sqlite3"
)

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
		line = strings.TrimSuffix(line, "\n")
		if err := w.c.insert(w.stream, line); err != nil {
			return len(p), err
		}
	}
	return len(p), nil
}

func (w *sqliteWriter) flush() error {
	if w.buf.Len() == 0 {
		return nil
	}
	line := strings.TrimRight(w.buf.String(), "\n")
	w.buf.Reset()
	return w.c.insert(w.stream, line)
}

type SQLiteLogCollector struct {
	db       *sql.DB
	stmt     *sql.Stmt
	ts       int64
	mu       sync.Mutex
	counters map[string]int
	writers  []*sqliteWriter
}

func NewSQLiteLogCollector(dsn string) (*SQLiteLogCollector, error) {
	db, err := sql.Open("sqlite3", dsn)
	if err != nil {
		return nil, err
	}
	table := `CREATE TABLE IF NOT EXISTS session_logs (
        session_ts INTEGER,
        stream     TEXT,
        line_num   INTEGER,
        text       TEXT
    )`
	if _, err = db.Exec(table); err != nil {
		db.Close()
		return nil, err
	}
	idx := `CREATE INDEX IF NOT EXISTS idx_session_line ON session_logs(session_ts, line_num)`
	if _, err = db.Exec(idx); err != nil {
		db.Close()
		return nil, err
	}
	stmt, err := db.Prepare(`INSERT INTO session_logs(session_ts,stream,line_num,text) VALUES(?,?,?,?)`)
	if err != nil {
		db.Close()
		return nil, err
	}
	return &SQLiteLogCollector{
		db:       db,
		stmt:     stmt,
		ts:       time.Now().UnixNano(),
		counters: map[string]int{},
	}, nil
}

func (s *SQLiteLogCollector) insert(stream, line string) error {
	s.mu.Lock()
	n := s.counters[stream] + 1
	s.counters[stream] = n
	s.mu.Unlock()
	_, err := s.stmt.Exec(s.ts, stream, n, line)
	return err
}

func (s *SQLiteLogCollector) Stream(name string) io.Writer {
	w := &sqliteWriter{c: s, stream: name}
	s.mu.Lock()
	s.writers = append(s.writers, w)
	s.mu.Unlock()
	return w
}

func (s *SQLiteLogCollector) Close() error {
	var err error
	for _, w := range s.writers {
		if e := w.flush(); e != nil && err == nil {
			err = e
		}
	}
	if s.stmt != nil {
		if e := s.stmt.Close(); e != nil && err == nil {
			err = e
		}
	}
	if s.db != nil {
		if e := s.db.Close(); e != nil && err == nil {
			err = e
		}
	}
	return err
}
