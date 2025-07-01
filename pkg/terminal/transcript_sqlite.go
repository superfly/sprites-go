package terminal

import (
	"database/sql"
	_ "embed"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"os"
	"path/filepath"
	"sync"
	"sync/atomic"
	"time"

	"github.com/google/uuid"
	_ "github.com/mattn/go-sqlite3"
)

//go:embed transcript_sqlite_schema.sql
var schemaSQL string

// SQLiteTranscript implements TranscriptCollector using SQLite backend.
type SQLiteTranscript struct {
	db        *sql.DB
	logger    *slog.Logger
	sessionID string
	env       []string
	tty       bool
	startTime time.Time
	sequence  int64 // Global sequence counter for all streams in this session
	mu        sync.Mutex
	closed    bool
}

type SQLiteTranscriptConfig struct {
	DBPath    string
	SessionID string
	Env       []string
	TTY       bool
	Logger    *slog.Logger
}

// NewSQLiteTranscript creates a new SQLite-based transcript collector.
func NewSQLiteTranscript(config SQLiteTranscriptConfig) (*SQLiteTranscript, error) {
	// Ensure directory exists
	dir := filepath.Dir(config.DBPath)
	if err := os.MkdirAll(dir, 0755); err != nil {
		return nil, fmt.Errorf("failed to create directory %s: %w", dir, err)
	}

	db, err := sql.Open("sqlite3", config.DBPath+"?_journal_mode=WAL&_foreign_keys=1")
	if err != nil {
		return nil, fmt.Errorf("failed to open SQLite database: %w", err)
	}

	if err := db.Ping(); err != nil {
		return nil, fmt.Errorf("failed to ping SQLite database: %w", err)
	}

	if err := initializeSchema(db); err != nil {
		return nil, fmt.Errorf("failed to initialize schema: %w", err)
	}

	sessionID := config.SessionID
	if sessionID == "" {
		sessionID = uuid.New().String()
	}

	logger := config.Logger
	if logger == nil {
		logger = slog.Default()
	}

	t := &SQLiteTranscript{
		db:        db,
		logger:    logger,
		sessionID: sessionID,
		env:       config.Env,
		tty:       config.TTY,
		startTime: time.Now(),
		sequence:  0,
	}

	// record the transcript session
	if err := t.createSession(); err != nil {
		return nil, fmt.Errorf("failed to create session: %w", err)
	}

	return t, nil
}

func initializeSchema(db *sql.DB) error {
	_, err := db.Exec(schemaSQL)
	return err
}

// createSession inserts a new session record into the database.
func (t *SQLiteTranscript) createSession() error {
	var envJSON *string
	if len(t.env) > 0 {
		envBytes, err := json.Marshal(t.env)
		if err != nil {
			return fmt.Errorf("failed to marshal environment: %w", err)
		}
		envStr := string(envBytes)
		envJSON = &envStr
	}

	query := `
		INSERT INTO sessions (session_id, start_time, working_dir, environment, tty)
		VALUES (?, ?, ?, ?, ?)
	`

	_, err := t.db.Exec(query,
		t.sessionID,
		t.startTime.UnixNano(),
		envJSON,
		t.tty,
	)
	if err != nil {
		return fmt.Errorf("failed to insert session: %w", err)
	}

	t.logger.Debug("Created session", "sessionID", t.sessionID)
	return nil
} // StreamWriter returns a writer for the named stream.
func (t *SQLiteTranscript) StreamWriter(name string) io.Writer {
	if t.closed {
		return io.Discard
	}

	// Validate stream name
	if name != "stdin" && name != "stdout" && name != "stderr" {
		t.logger.Warn("Invalid stream name", "stream", name)
		return io.Discard
	}

	return &sqliteStreamWriter{transcript: t, streamName: name}
}

// Remove createStream - no longer needed since we don't have a streams table// Close closes the transcript and updates session end time.
func (t *SQLiteTranscript) Close() error {
	t.mu.Lock()
	defer t.mu.Unlock()

	if t.closed {
		return nil
	}

	t.closed = true

	// Update session end time
	query := `UPDATE sessions SET end_time = ? WHERE session_id = ?`
	_, err := t.db.Exec(query, time.Now().UnixNano(), t.sessionID)
	if err != nil {
		t.logger.Error("Failed to update session end time", "error", err)
	}

	// No streams to close in simplified schema

	// Close database
	if dbErr := t.db.Close(); dbErr != nil {
		t.logger.Error("Failed to close database", "error", dbErr)
		if err == nil {
			err = dbErr
		}
	}

	t.logger.Debug("Closed transcript", "sessionID", t.sessionID)
	return err
}

// SetExitCode updates the session's exit code.
func (t *SQLiteTranscript) SetExitCode(code int) error {
	t.mu.Lock()
	defer t.mu.Unlock()

	if t.closed {
		return fmt.Errorf("transcript is closed")
	}

	query := `UPDATE sessions SET exit_code = ? WHERE session_id = ?`
	_, err := t.db.Exec(query, code, t.sessionID)
	if err != nil {
		return fmt.Errorf("failed to update exit code: %w", err)
	}

	t.logger.Debug("Updated exit code", "sessionID", t.sessionID, "exitCode", code)
	return nil
}

// GetSessionID returns the session ID for this transcript.
func (t *SQLiteTranscript) GetSessionID() string {
	return t.sessionID
}

// sqliteStreamWriter implements io.Writer for a specific stream.
type sqliteStreamWriter struct {
	transcript *SQLiteTranscript
	streamName string
}

// Write implements io.Writer by writing data line by line to the database.
func (w *sqliteStreamWriter) Write(p []byte) (int, error) {
	if w.transcript == nil || w.transcript.closed {
		return len(p), nil // Silently discard if closed
	}

	// Split data into lines and write each line separately
	data := string(p)
	lines := splitIntoLines(data)

	for _, line := range lines {
		if line == "" {
			continue // Skip empty lines
		}

		if err := w.writeLogLine(line); err != nil {
			w.transcript.logger.Error("Failed to write log line", "error", err)
			// Continue processing other lines even if one fails
		}
	}

	return len(p), nil
}

// writeLogLine writes a single log line to the database.
func (w *sqliteStreamWriter) writeLogLine(message string) error {
	lineID := uuid.New().String()
	sequence := atomic.AddInt64(&w.transcript.sequence, 1)
	timestamp := time.Now().UnixNano()

	query := `
		INSERT INTO log_lines (line_id, session_id, stream, sequence, timestamp, message)
		VALUES (?, ?, ?, ?, ?, ?)
	`

	_, err := w.transcript.db.Exec(query, lineID, w.transcript.sessionID, w.streamName, sequence, timestamp, message)
	if err != nil {
		return fmt.Errorf("failed to insert log line: %w", err)
	}

	w.transcript.logger.Debug("Wrote log line",
		"lineID", lineID,
		"sessionID", w.transcript.sessionID,
		"stream", w.streamName,
		"sequence", sequence,
		"message", message)

	return nil
}

// splitIntoLines splits data into individual lines, preserving partial lines.
func splitIntoLines(data string) []string {
	if data == "" {
		return nil
	}

	// Simple line splitting - in a production system you might want
	// more sophisticated handling of partial lines and different line endings
	lines := []string{}
	currentLine := ""

	for _, char := range data {
		if char == '\n' {
			lines = append(lines, currentLine)
			currentLine = ""
		} else if char != '\r' { // Skip carriage returns
			currentLine += string(char)
		}
	}

	// Add remaining partial line if any
	if currentLine != "" {
		lines = append(lines, currentLine)
	}

	return lines
}
