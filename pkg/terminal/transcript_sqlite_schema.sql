-- SQLite schema for transcript logging
-- Simplified schema focusing on essential data

CREATE TABLE IF NOT EXISTS sessions (
    session_id TEXT PRIMARY KEY,
    start_time INTEGER NOT NULL, -- Unix timestamp in nanoseconds
    end_time INTEGER DEFAULT NULL, -- Unix timestamp in nanoseconds, NULL if still active
    working_dir TEXT DEFAULT NULL,
    environment TEXT DEFAULT NULL, -- JSON encoded environment variables
    tty BOOLEAN NOT NULL DEFAULT FALSE,
    exit_code INTEGER DEFAULT NULL, -- NULL if still running
    created_at INTEGER NOT NULL DEFAULT (unixepoch() * 1000000000), -- nanoseconds
    updated_at INTEGER NOT NULL DEFAULT (unixepoch() * 1000000000) -- nanoseconds
);

CREATE TABLE IF NOT EXISTS log_lines (
    line_id TEXT PRIMARY KEY,
    session_id TEXT NOT NULL,
    stream TEXT NOT NULL, -- 'stdin', 'stdout', 'stderr'
    sequence INTEGER NOT NULL, -- Line sequence number within the session
    timestamp INTEGER NOT NULL, -- Unix timestamp in nanoseconds when line was recorded
    message TEXT NOT NULL, -- The actual log line content
    created_at INTEGER NOT NULL DEFAULT (unixepoch() * 1000000000), -- nanoseconds
    FOREIGN KEY (session_id) REFERENCES sessions(session_id) ON DELETE CASCADE
);

-- Indexes for performance
CREATE INDEX IF NOT EXISTS idx_log_lines_session_id ON log_lines(session_id);
CREATE INDEX IF NOT EXISTS idx_log_lines_stream ON log_lines(stream);
CREATE INDEX IF NOT EXISTS idx_log_lines_timestamp ON log_lines(timestamp);
CREATE INDEX IF NOT EXISTS idx_log_lines_sequence ON log_lines(session_id, sequence);
CREATE INDEX IF NOT EXISTS idx_sessions_start_time ON sessions(start_time);

-- Trigger to update updated_at on sessions table
CREATE TRIGGER IF NOT EXISTS sessions_updated_at 
AFTER UPDATE ON sessions
BEGIN
    UPDATE sessions SET updated_at = unixepoch() * 1000000000 WHERE session_id = NEW.session_id;
END;
