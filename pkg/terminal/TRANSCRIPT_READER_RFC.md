# Transcript Reader API - Implementation

This document presents the implemented solution for the ergonomic transcript API RFC, redesigned to support database backends and HTTP polling use cases.

## API Design

### Core Types

```go
// TranscriptLine represents a single line from a transcript with metadata.
type TranscriptLine struct {
    // SessionID uniquely identifies the session this line belongs to
    SessionID string `json:"session_id"`
    // Sequence is the line number within the session (starts at 1)
    Sequence int64 `json:"sequence"`
    // Timestamp when the line was recorded
    Timestamp time.Time `json:"timestamp"`
    // Stream identifies the I/O stream ("stdin", "stdout", "stderr")
    Stream string `json:"stream"`
    // Text is the actual line content
    Text string `json:"text"`
}

// LineQuery specifies criteria for retrieving transcript lines.
type LineQuery struct {
    // SessionID to query (required)
    SessionID string
    // AfterSequence returns only lines with sequence > this value (0 = from beginning)
    AfterSequence int64
    // Stream filter ("stdin", "stdout", "stderr", "all"). Default: "all"
    Stream string
    // Limit maximum number of lines to return (0 = no limit)
    Limit int
    // Follow indicates whether to wait for new lines (live streaming)
    Follow bool
}
```

### Core Interface

```go
// TranscriptReader provides a unified interface for reading transcript data
// in both post-mortem and live streaming modes.
type TranscriptReader interface {
    // NextLine returns the next line from the transcript.
    // Returns io.EOF when the transcript is complete and no more lines are available.
    // For live streams, this method blocks until a line is available or the context is cancelled.
    NextLine(ctx context.Context) (*TranscriptLine, error)

    // NextLineAfter returns the next line with sequence number greater than the specified value.
    // This is useful for polling scenarios where clients want to resume from a known position.
    NextLineAfter(ctx context.Context, afterSequence int64) (*TranscriptLine, error)

    // GetLines retrieves multiple lines at once, useful for batch operations.
    GetLines(ctx context.Context, query LineQuery) ([]TranscriptLine, error)

    // SessionID returns the session ID this reader is associated with.
    SessionID() string

    // Close releases any resources associated with the reader.
    Close() error
}
```

### Backend Interface

```go
// TranscriptBackend defines the interface for different storage backends.
type TranscriptBackend interface {
    // GetLines retrieves transcript lines matching the query
    GetLines(ctx context.Context, query LineQuery) ([]TranscriptLine, error)
    // Close releases any resources associated with the backend
    Close() error
}
```

### Configuration

```go
type TranscriptReaderConfig struct {
    // BufferSize controls the internal line buffer size for live streams (default: 100)
    BufferSize int
    // FlushInterval controls how often buffered lines are made available (default: 1s)
    FlushInterval time.Duration
    // Stream specifies which stream to read ("stdout", "stderr", "all"). Default: "all"
    Stream string
}
```

### Factory Functions

#### Backend-agnostic Mode
```go
// Open a transcript using any backend
func OpenTranscript(sessionID string, backend TranscriptBackend) (TranscriptReader, error)
func OpenTranscriptWithConfig(sessionID string, backend TranscriptBackend, config TranscriptReaderConfig) (TranscriptReader, error)
```

#### File-based Mode (Convenience)
```go
// Open a completed transcript file (legacy compatibility)
func OpenTranscriptFile(path string) (TranscriptReader, error)
func OpenTranscriptFileWithConfig(path string, config TranscriptReaderConfig) (TranscriptReader, error)
```

#### Live Streaming Mode
```go
// Stream from a running command (generates new session ID)
func StreamTranscript(ctx context.Context, cmd *exec.Cmd) (TranscriptReader, error)
func StreamTranscriptWithConfig(ctx context.Context, cmd *exec.Cmd, config TranscriptReaderConfig) (TranscriptReader, error)

// Stream with specific session ID
func StreamTranscriptWithSession(ctx context.Context, sessionID string, cmd *exec.Cmd, config TranscriptReaderConfig) (TranscriptReader, error)

// Stream from a MemoryTranscript (useful for testing)
func StreamMemoryTranscript(ctx context.Context, sessionID string, transcript *MemoryTranscript) TranscriptReader
func StreamMemoryTranscriptWithConfig(ctx context.Context, sessionID string, transcript *MemoryTranscript, config TranscriptReaderConfig) TranscriptReader
```

#### Backend Implementations
```go
// File-based backend
func NewFileTranscriptBackend(path string) (TranscriptBackend, error)

// Memory-based backend
func NewMemoryTranscriptBackend(sessionID string, transcript *MemoryTranscript) TranscriptBackend
```

## Usage Examples

### 1. Post-mortem Reading

```go
func readCompletedTranscript() {
    tr, err := terminal.OpenTranscriptFile("session.log")
    if err != nil {
        log.Fatal(err)
    }
    defer tr.Close()

    fmt.Printf("Reading session: %s\n", tr.SessionID())
    
    ctx := context.Background()
    for {
        line, err := tr.NextLine(ctx)
        if err == io.EOF {
            break // End of transcript
        }
        if err != nil {
            log.Printf("Error reading line: %v", err)
            break
        }
        fmt.Printf("[%s] Seq %d [%s]: %s\n", 
            line.Timestamp.Format("15:04:05"), 
            line.Sequence, 
            line.Stream, 
            line.Text)
    }
}
```

### 2. Live Streaming

```go
func streamLiveTranscript() {
    ctx, cancel := context.WithCancel(context.Background())
    defer cancel()

    cmd := exec.Command("make", "build")
    tr, err := terminal.StreamTranscript(ctx, cmd)
    if err != nil {
        log.Fatal(err)
    }
    defer tr.Close()

    fmt.Printf("Streaming session: %s\n", tr.SessionID())
    
    for {
        line, err := tr.NextLine(ctx)
        if err == io.EOF {
            break // Command completed
        }
        if err != nil {
            log.Printf("Error reading line: %v", err)
            break
        }
        fmt.Printf("BUILD Seq %d [%s]: %s\n", line.Sequence, line.Stream, line.Text)
    }
}
```

### 3. HTTP API Polling Pattern

```go
func httpPollingExample() {
    ctx := context.Background()
    
    // Start a session (could be from HTTP request)
    cmd := exec.Command("make", "test")
    tr, err := terminal.StreamTranscript(ctx, cmd)
    if err != nil {
        log.Fatal(err)
    }
    defer tr.Close()
    
    sessionID := tr.SessionID()
    fmt.Printf("Session ID: %s\n", sessionID)
    
    // Simulate HTTP polling clients
    lastSequence := int64(0)
    
    for pollCount := 1; pollCount <= 3; pollCount++ {
        fmt.Printf("\n=== Poll %d ===\n", pollCount)
        
        // Get only new lines since last poll
        query := terminal.LineQuery{
            SessionID:     sessionID,
            AfterSequence: lastSequence,
            Stream:        "all",
            Limit:         10,
            Follow:        false, // Don't wait, return what's available
        }
        
        lines, err := tr.GetLines(ctx, query)
        if err != nil {
            log.Printf("Error: %v", err)
            continue
        }
        
        fmt.Printf("Found %d new lines since sequence %d\n", len(lines), lastSequence)
        for _, line := range lines {
            fmt.Printf("  Seq %d [%s]: %s\n", line.Sequence, line.Stream, line.Text)
            lastSequence = line.Sequence
        }
        
        // Simulate delay between polls
        time.Sleep(1 * time.Second)
    }
}
```

### 4. Database Backend Usage

```go
func databaseBackendExample() {
    // This shows how to use the API with a hypothetical database backend
    // (actual SQLite/Parquet implementations would come later)
    
    sessionID := "550e8400-e29b-41d4-a716-446655440000"
    
    // Hypothetical database backend
    // backend := NewSQLiteTranscriptBackend("transcripts.db")
    // defer backend.Close()
    
    // tr, err := terminal.OpenTranscript(sessionID, backend)
    // if err != nil {
    //     log.Fatal(err)
    // }
    // defer tr.Close()
    
    ctx := context.Background()
    
    // Get lines from a specific point in time
    query := terminal.LineQuery{
        SessionID:     sessionID,
        AfterSequence: 100, // Resume from sequence 100
        Stream:        "stderr", // Only stderr
        Limit:         50,
        Follow:        false,
    }
    
    // lines, err := tr.GetLines(ctx, query)
    // Process database results...
}
```

### 5. Unified Processing Function

```go
// This function works with both post-mortem and live readers
func processTranscript(tr terminal.TranscriptReader) {
    ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
    defer cancel()
    
    fmt.Printf("Processing session: %s\n", tr.SessionID())
    
    lineCount := 0
    for {
        line, err := tr.NextLine(ctx)
        if err == io.EOF {
            break
        }
        if err != nil {
            log.Printf("Error: %v", err)
            break
        }
        lineCount++
        fmt.Printf("Line %d [seq=%d, %s]: %s\n", lineCount, line.Sequence, line.Stream, line.Text)
    }
    fmt.Printf("Total lines processed: %d\n", lineCount)
}

// Use with either mode:
// liveReader, _ := terminal.StreamTranscript(ctx, cmd)
// processTranscript(liveReader)
//
// fileReader, _ := terminal.OpenTranscriptFile("session.log")
// processTranscript(fileReader)
```

### 4. Stream Filtering

```go
func readOnlyStderr() {
    ctx := context.Background()
    
    config := terminal.TranscriptReaderConfig{
        BufferSize:    200,
        FlushInterval: 500 * time.Millisecond,
        Stream:        "stderr", // Only read stderr
    }
    
    cmd := exec.Command("gcc", "bad_code.c")
    tr, err := terminal.StreamTranscriptWithConfig(ctx, cmd, config)
    if err != nil {
        log.Fatal(err)
    }
    defer tr.Close()
    
    for {
        line, err := tr.NextLine(ctx)
        if err == io.EOF {
            break
        }
        if err != nil {
            log.Printf("Error: %v", err)
            break
        }
        fmt.Printf("COMPILE ERROR: %s\n", line)
    }
}
```

### 5. Integration with Terminal Sessions

```go
func sessionWithLiveTranscript() {
    ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
    defer cancel()

    // Create a memory transcript to collect session output
    transcript := terminal.NewMemoryTranscript()

    // Create and run a terminal session
    session := terminal.NewSession(
        terminal.WithCommand("npm", "test"),
        terminal.WithTTY(false),
        terminal.WithTranscript(transcript),
    )

    // Start streaming the transcript
    tr := terminal.StreamMemoryTranscript(ctx, transcript)
    defer tr.Close()

    // Run session in background
    go func() {
        stdin := strings.NewReader("")
        var stdout, stderr strings.Builder
        session.Run(ctx, stdin, &stdout, &stderr)
    }()

    // Stream output in real-time
    for {
        line, err := tr.NextLine(ctx)
        if err == io.EOF {
            break
        }
        if err != nil {
            log.Printf("Error: %v", err)
            break
        }
        fmt.Printf("TEST: %s\n", line)
    }
}
```

## Design Decisions

### 1. Database-Ready Architecture
- **Session UUIDs**: Every transcript is identified by a unique session ID, enabling database storage
- **Structured line data**: `TranscriptLine` struct contains all metadata needed for database storage
- **Sequence numbers**: Enable efficient "give me lines after N" queries for polling
- **Backend abstraction**: `TranscriptBackend` interface supports SQLite, Parquet, files, memory, etc.

### 2. HTTP Polling Support
- **`NextLineAfter()`**: Clients can request "lines after sequence N" for efficient polling
- **`GetLines()` with queries**: Batch operations with filtering and limits
- **Position tracking**: Sequence numbers enable clients to resume from last known position
- **Stream filtering**: Support for "only stderr" or "only stdout" queries

### 3. Go-Idiomatic Design
- **Structured return types**: `NextLine(ctx) (*TranscriptLine, error)` provides rich metadata
- **Context support**: All reading operations accept `context.Context` for cancellation and timeouts
- **io.EOF semantics**: Uses standard Go EOF signaling for end-of-stream
- **Resource management**: `Close()` method for explicit cleanup

### 4. Unified API Surface
- **Single interface**: Both modes implement the same `TranscriptReader` interface
- **Backend flexibility**: Same interface works with files, memory, databases
- **Consistent behavior**: Same error handling and cancellation semantics across modes

### 5. Thread Safety & Performance
- **Concurrent access**: All implementations are thread-safe
- **Goroutine coordination**: Uses channels and mutexes appropriately
- **Context cancellation**: Respects context cancellation across all operations
- **Efficient parsing**: Smart log line parsing handles quoted content correctly

## Implementation Details

### File-based Reader (Post-mortem)
- Parses structured log files created by `FileTranscript`
- Extracts transcript lines from slog format
- Supports stream filtering (stdout/stderr/all)
- Thread-safe with mutex protection

### Live Command Reader
- Captures stdout/stderr from running commands
- Uses separate goroutines for each stream
- Coordinates command lifecycle with transcript reading
- Buffers lines in channels for smooth delivery

### Memory Transcript Reader
- Polls `MemoryTranscript` at configurable intervals
- Tracks read position per stream
- Supports real-time addition of new content
- Useful for testing and in-memory scenarios

## Testing

The implementation includes comprehensive tests covering:
- Post-mortem file reading
- Live command streaming
- Memory transcript streaming
- Stream filtering
- Context cancellation
- Resource cleanup
- Error conditions

## Migration and Compatibility

This API is purely additive and does not affect existing transcript collection functionality. The current `TranscriptCollector` interface remains unchanged, and this new API provides the missing read-side functionality.

## Database Backend Implementation Notes

The current implementation provides file and memory backends. Future database backends should:

### SQLite Backend
```sql
CREATE TABLE transcript_lines (
    session_id TEXT NOT NULL,
    sequence INTEGER NOT NULL,
    timestamp TEXT NOT NULL,
    stream TEXT NOT NULL,
    text TEXT NOT NULL,
    PRIMARY KEY (session_id, sequence)
);

CREATE INDEX idx_session_sequence ON transcript_lines(session_id, sequence);
CREATE INDEX idx_session_stream ON transcript_lines(session_id, stream);
```

### Parquet Schema
```
message TranscriptLine {
  required binary session_id (UTF8);
  required int64 sequence;
  required int64 timestamp (TIMESTAMP_MILLIS);
  required binary stream (UTF8);
  required binary text (UTF8);
}
```

### Implementation Pattern
```go
type SQLiteTranscriptBackend struct {
    db *sql.DB
}

func (b *SQLiteTranscriptBackend) GetLines(ctx context.Context, query LineQuery) ([]TranscriptLine, error) {
    sql := `SELECT session_id, sequence, timestamp, stream, text 
            FROM transcript_lines 
            WHERE session_id = ? AND sequence > ?
            ORDER BY sequence ASC`
    
    if query.Stream != "all" {
        sql += " AND stream = ?"
    }
    if query.Limit > 0 {
        sql += " LIMIT ?"
    }
    
    // Execute query and return results...
}
```

## Future Considerations

1. **Database backends**: SQLite and Parquet implementations as described above
2. **Performance optimization**: Prepared statements, connection pooling for database backends
3. **Compression**: Parquet provides natural compression for large transcript storage
4. **Retention policies**: Automatic cleanup of old sessions
5. **Indexing strategies**: Optimize for common query patterns (session+sequence, session+stream)
6. **Streaming inserts**: Efficient real-time insertion for live transcripts
