package terminal

import (
	"context"
	"database/sql"
	"fmt"
	"io"
	"time"

	_ "github.com/mattn/go-sqlite3"
)

// sqliteTranscriptBackend implements TranscriptBackend for SQLite storage.
type sqliteTranscriptBackend struct {
	db     *sql.DB
	dbPath string
}

// NewSQLiteTranscriptBackend creates a new SQLite backend for reading transcripts.
func NewSQLiteTranscriptBackend(dbPath string) (TranscriptBackend, error) {
	// Open database in read-only mode for safety
	db, err := sql.Open("sqlite3", dbPath+"?mode=ro&_journal_mode=WAL")
	if err != nil {
		return nil, fmt.Errorf("failed to open SQLite database: %w", err)
	}

	// Test connection
	if err := db.Ping(); err != nil {
		return nil, fmt.Errorf("failed to ping SQLite database: %w", err)
	}

	return &sqliteTranscriptBackend{
		db:     db,
		dbPath: dbPath,
	}, nil
}

// GetLines retrieves transcript lines matching the query.
func (b *sqliteTranscriptBackend) GetLines(ctx context.Context, query LineQuery) ([]TranscriptLine, error) {
	// Build SQL query based on LineQuery parameters
	sqlQuery := `
		SELECT 
			ll.sequence,
			ll.timestamp,
			ll.stream,
			ll.message
		FROM log_lines ll
		WHERE ll.session_id = ?
	`

	args := []interface{}{query.SessionID}

	// Add sequence filter
	if query.AfterSequence > 0 {
		sqlQuery += " AND ll.sequence > ?"
		args = append(args, query.AfterSequence)
	}

	// Add stream filter
	if query.Stream != "" && query.Stream != "all" {
		sqlQuery += " AND ll.stream = ?"
		args = append(args, query.Stream)
	}

	// Order by sequence
	sqlQuery += " ORDER BY ll.sequence ASC"

	// Add limit
	if query.Limit > 0 {
		sqlQuery += " LIMIT ?"
		args = append(args, query.Limit)
	}

	// Execute query with context
	rows, err := b.db.QueryContext(ctx, sqlQuery, args...)
	if err != nil {
		return nil, fmt.Errorf("failed to query log lines: %w", err)
	}
	defer rows.Close()

	var lines []TranscriptLine
	for rows.Next() {
		select {
		case <-ctx.Done():
			return nil, ctx.Err()
		default:
		}

		var (
			sequence  int64
			timestamp int64 // nanoseconds
			stream    string
			message   string
		)

		if err := rows.Scan(&sequence, &timestamp, &stream, &message); err != nil {
			return nil, fmt.Errorf("failed to scan log line: %w", err)
		}

		lines = append(lines, TranscriptLine{
			SessionID: query.SessionID,
			Sequence:  sequence,
			Timestamp: time.Unix(0, timestamp),
			Stream:    stream,
			Text:      message,
		})
	}

	if err := rows.Err(); err != nil {
		return nil, fmt.Errorf("row iteration error: %w", err)
	}

	// Handle Follow mode - for SQLite backend, we don't support live following
	// since it's primarily for post-mortem analysis. Live following would require
	// polling or file watching which is beyond the scope of this implementation.
	if query.Follow && len(lines) == 0 {
		return nil, io.EOF
	}

	return lines, nil
}

// Close releases any resources associated with the backend.
func (b *sqliteTranscriptBackend) Close() error {
	if b.db != nil {
		err := b.db.Close()
		b.db = nil
		return err
	}
	return nil
}

// GetSessionInfo retrieves session metadata.
func (b *sqliteTranscriptBackend) GetSessionInfo(ctx context.Context, sessionID string) (*SessionInfo, error) {
	query := `
		SELECT 
			session_id,
			start_time,
			end_time,
			working_dir,
			environment,
			tty,
			exit_code
		FROM sessions
		WHERE session_id = ?
	`

	row := b.db.QueryRowContext(ctx, query, sessionID)

	var (
		sid         string
		startTime   int64
		endTime     *int64
		workingDir  *string
		environment *string
		tty         bool
		exitCode    *int
	)

	err := row.Scan(&sid, &startTime, &endTime, &workingDir, &environment, &tty, &exitCode)
	if err != nil {
		if err == sql.ErrNoRows {
			return nil, fmt.Errorf("session not found: %s", sessionID)
		}
		return nil, fmt.Errorf("failed to query session info: %w", err)
	}

	sessionInfo := &SessionInfo{
		SessionID: sid,
		StartTime: time.Unix(0, startTime),
		TTY:       tty,
	}

	if endTime != nil {
		endTimeVal := time.Unix(0, *endTime)
		sessionInfo.EndTime = &endTimeVal
	}

	if workingDir != nil {
		sessionInfo.WorkingDir = *workingDir
	}

	if environment != nil {
		sessionInfo.Environment = *environment
	}

	if exitCode != nil {
		sessionInfo.ExitCode = *exitCode
	}

	return sessionInfo, nil
}

// ListSessions retrieves a list of sessions with optional filtering.
func (b *sqliteTranscriptBackend) ListSessions(ctx context.Context, limit int, offset int) ([]SessionInfo, error) {
	query := `
		SELECT 
			session_id,
			start_time,
			end_time,
			working_dir,
			environment,
			tty,
			exit_code
		FROM sessions
		ORDER BY start_time DESC
	`

	args := []interface{}{}

	if limit > 0 {
		query += " LIMIT ?"
		args = append(args, limit)
	}

	if offset > 0 {
		query += " OFFSET ?"
		args = append(args, offset)
	}

	rows, err := b.db.QueryContext(ctx, query, args...)
	if err != nil {
		return nil, fmt.Errorf("failed to query sessions: %w", err)
	}
	defer rows.Close()

	var sessions []SessionInfo
	for rows.Next() {
		select {
		case <-ctx.Done():
			return nil, ctx.Err()
		default:
		}

		var (
			sid         string
			startTime   int64
			endTime     *int64
			workingDir  *string
			environment *string
			tty         bool
			exitCode    *int
		)

		if err := rows.Scan(&sid, &startTime, &endTime, &workingDir, &environment, &tty, &exitCode); err != nil {
			return nil, fmt.Errorf("failed to scan session: %w", err)
		}

		sessionInfo := SessionInfo{
			SessionID: sid,
			StartTime: time.Unix(0, startTime),
			TTY:       tty,
		}
		if endTime != nil {
			endTimeVal := time.Unix(0, *endTime)
			sessionInfo.EndTime = &endTimeVal
		}

		if workingDir != nil {
			sessionInfo.WorkingDir = *workingDir
		}

		if environment != nil {
			sessionInfo.Environment = *environment
		}

		if exitCode != nil {
			sessionInfo.ExitCode = *exitCode
		}

		sessions = append(sessions, sessionInfo)
	}

	if err := rows.Err(); err != nil {
		return nil, fmt.Errorf("row iteration error: %w", err)
	}

	return sessions, nil
}

// SessionInfo represents metadata about a transcript session.
type SessionInfo struct {
	SessionID   string     `json:"session_id"`
	StartTime   time.Time  `json:"start_time"`
	EndTime     *time.Time `json:"end_time,omitempty"`
	WorkingDir  string     `json:"working_dir,omitempty"`
	Environment string     `json:"environment,omitempty"`
	TTY         bool       `json:"tty"`
	ExitCode    int        `json:"exit_code,omitempty"`
}
