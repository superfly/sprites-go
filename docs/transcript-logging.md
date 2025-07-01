# Transcript Logging

This document describes the SQLite-based transcript logging system for capturing session I/O.

## Overview

The transcript logging system captures session I/O (stdin, stdout, stderr) and stores it in a SQLite database for later analysis. The system uses a simple, efficient schema designed for fast writes and flexible querying.

## Quick Start

### Default Configuration

By default, transcript logging is enabled with SQLite backend:

```bash
# Default behavior - SQLite backend at /var/log/transcripts.db
./sprite-env-server
```

### Environment Variable Configuration

```bash
# Configure database path
export SPRITE_TRANSCRIPT_DB_PATH="/custom/path/transcripts.db"

./sprite-env-server
```

### JSON Configuration File

```json
{
  "transcript_db_path": "/var/log/transcripts.db"
}
```

Run with config file:
```bash
./sprite-env-server -config config.json
```

## Configuration Options

| Setting | Environment Variable | JSON Key | Default | Description |
|---------|---------------------|----------|---------|-------------|
| Database Path | `SPRITE_TRANSCRIPT_DB_PATH` | `transcript_db_path` | `/var/log/transcripts.db` | Path to SQLite database file |

### Global Transcript Control

Transcripts can be enabled/disabled at runtime via the HTTP API:

```bash
# Enable transcripts
curl -X POST "http://localhost:8080/api/transcripts/enable" \
     -H "Authorization: Bearer $SPRITE_HTTP_API_TOKEN"

# Disable transcripts
curl -X POST "http://localhost:8080/api/transcripts/disable" \
     -H "Authorization: Bearer $SPRITE_HTTP_API_TOKEN"
```

## Database Schema

The SQLite backend uses a simple two-table schema:

### Sessions Table
Stores metadata about each execution session:
- `session_id` (TEXT, PRIMARY KEY) - Unique session identifier
- `start_time` (INTEGER) - Session start timestamp (nanoseconds)
- `end_time` (INTEGER, NULLABLE) - Session end timestamp (nanoseconds)
- `working_dir` (TEXT, NULLABLE) - Working directory
- `environment` (TEXT, NULLABLE) - JSON-encoded environment variables
- `tty` (BOOLEAN) - Whether TTY mode was enabled
- `exit_code` (INTEGER, NULLABLE) - Command exit code
- `created_at` (INTEGER) - Record creation timestamp
- `updated_at` (INTEGER) - Record update timestamp

### Log Lines Table
Stores individual log lines:
- `line_id` (TEXT, PRIMARY KEY) - Unique line identifier
- `session_id` (TEXT, FOREIGN KEY) - Reference to parent session
- `stream` (TEXT) - Stream type: "stdin", "stdout", or "stderr"
- `sequence` (INTEGER) - Line sequence number within the session
- `timestamp` (INTEGER) - Line timestamp (nanoseconds)
- `message` (TEXT) - The actual log line content
- `created_at` (INTEGER) - Record creation timestamp

### Performance Optimizations

The SQLite backend includes several optimizations:

1. **WAL Mode**: Uses Write-Ahead Logging for better concurrency
2. **Foreign Keys**: Enabled for data integrity
3. **Indexes**: Optimized for common query patterns:
   - `idx_log_lines_session_id` - Fast session → lines lookup
   - `idx_log_lines_stream` - Stream-based filtering
   - `idx_log_lines_timestamp` - Time-based queries
   - `idx_log_lines_sequence` - Sequence-based queries
   - `idx_sessions_start_time` - Session listing by time

## Requirements

The SQLite backend requires CGO to be enabled during compilation:

```bash
# Build with CGO enabled
CGO_ENABLED=1 go build .
```

If CGO is not available, the system will fail to start (this is by design - no fallback to ensure data consistency).

## Usage Examples

### Reading Transcripts Programmatically

```go
// Create backend for reading
backend, err := terminal.NewSQLiteTranscriptBackend("/var/log/transcripts.db")
if err != nil {
    return err
}
defer backend.Close()

// Query log lines
query := terminal.LineQuery{
    SessionID:     "session-uuid",
    Stream:        "stdout", // or "stderr", "stdin", "all"
    Limit:         100,
    AfterSequence: 0, // Start from beginning
}

lines, err := backend.GetLines(context.Background(), query)
if err != nil {
    return err
}

for _, line := range lines {
    fmt.Printf("[%s] %s: %s\n", line.Timestamp.Format(time.RFC3339), line.Stream, line.Text)
}

// Get session information
sqliteBackend := backend.(*terminal.SQLiteTranscriptBackend)
sessionInfo, err := sqliteBackend.GetSessionInfo(context.Background(), "session-uuid")
if err != nil {
    return err
}

fmt.Printf("Session %s: TTY=%v, Exit Code=%d\n", sessionInfo.SessionID, sessionInfo.TTY, sessionInfo.ExitCode)

// List all sessions
sessions, err := sqliteBackend.ListSessions(context.Background(), 10, 0) // limit=10, offset=0
if err != nil {
    return err
}

for _, session := range sessions {
    fmt.Printf("Session %s (exit: %d)\n", session.SessionID, session.ExitCode)
}
```

## Maintenance

### Database Backup
```bash
# Create backup
sqlite3 /var/log/transcripts.db ".backup /backup/transcripts-$(date +%Y%m%d).db"

# Restore from backup
sqlite3 /var/log/transcripts.db ".restore /backup/transcripts-20241201.db"
```

### Database Optimization
```bash
# Analyze and optimize
sqlite3 /var/log/transcripts.db "ANALYZE; VACUUM;"
```

### Size Monitoring
```bash
# Check database size
du -h /var/log/transcripts.db

# Check table sizes
sqlite3 /var/log/transcripts.db "
SELECT 
    'sessions' as table_name,
    COUNT(*) as row_count
FROM sessions
UNION ALL
SELECT 
    'log_lines' as table_name,
    COUNT(*) as row_count
FROM log_lines;
"
```

### Cleanup Old Sessions
```bash
# Clean up sessions older than 30 days
sqlite3 /var/log/transcripts.db "
DELETE FROM sessions 
WHERE start_time < (unixepoch() - 30*24*60*60) * 1000000000;
"
```

## Troubleshooting

### Common Issues

#### SQLite Database Permission Errors
```bash
# Ensure directory exists and is writable
sudo mkdir -p /var/log
sudo chown $USER:$USER /var/log

# Or use a user-writable location
export SPRITE_TRANSCRIPT_DB_PATH="$HOME/transcripts.db"
```

#### Database Locked Errors
If you see "database is locked" errors:

1. Check for stale processes:
   ```bash
   lsof /var/log/transcripts.db
   ```

2. Ensure WAL mode is properly configured (this is automatic)

#### Disk Space Issues
```bash
# Check available space
df -h /var/log

# Clean up old sessions if needed
sqlite3 /var/log/transcripts.db "
DELETE FROM sessions 
WHERE start_time < (unixepoch() - 7*24*60*60) * 1000000000; -- 7 days ago
"
```

### Debugging

Enable debug logging to troubleshoot transcript issues:

```bash
export SPRITE_LOG_LEVEL=debug
./sprite-env-server
```

This will show detailed logging about transcript creation, writing, and any errors.

### Monitoring

Monitor transcript system health:

```bash
# Check recent sessions
sqlite3 /var/log/transcripts.db "
SELECT 
    session_id,
    datetime(start_time/1000000000, 'unixepoch') as start_time,
    exit_code
FROM sessions 
ORDER BY start_time DESC 
LIMIT 10;
"

# Check session count by day
sqlite3 /var/log/transcripts.db "
SELECT 
    date(start_time/1000000000, 'unixepoch') as date,
    COUNT(*) as session_count
FROM sessions 
GROUP BY date(start_time/1000000000, 'unixepoch')
ORDER BY date DESC;
"
```

## Design Philosophy

This implementation prioritizes:

1. **Simplicity** - Two-table schema, hardcoded SQLite backend
2. **Performance** - Optimized for high-frequency writes with minimal metadata
3. **Reliability** - Fail fast if SQLite is unavailable rather than silently degrade
4. **Future-proofing** - Structured data with unique IDs for eventual API access

The system is designed to handle millions of log lines efficiently while providing flexible querying capabilities for analysis and debugging.
