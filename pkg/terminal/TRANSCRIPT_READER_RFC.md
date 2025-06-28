# Transcript Reader API - Implementation

This document presents the implemented solution for the ergonomic transcript API RFC.

## API Design

### Core Interface

```go
// TranscriptReader provides a unified interface for reading transcript data
// in both post-mortem and live streaming modes.
type TranscriptReader interface {
    // NextLine returns the next line from the transcript.
    // Returns io.EOF when the transcript is complete and no more lines are available.
    // For live streams, this method blocks until a line is available or the context is cancelled.
    NextLine(ctx context.Context) (string, error)

    // Close releases any resources associated with the reader.
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

#### Post-mortem Mode
```go
// Open a completed transcript file
func OpenTranscript(path string) (TranscriptReader, error)
func OpenTranscriptWithConfig(path string, config TranscriptReaderConfig) (TranscriptReader, error)
```

#### Live Streaming Mode
```go
// Stream from a running command
func StreamTranscript(ctx context.Context, cmd *exec.Cmd) (TranscriptReader, error)
func StreamTranscriptWithConfig(ctx context.Context, cmd *exec.Cmd, config TranscriptReaderConfig) (TranscriptReader, error)

// Stream from a MemoryTranscript (useful for testing)
func StreamMemoryTranscript(ctx context.Context, transcript *MemoryTranscript) TranscriptReader
func StreamMemoryTranscriptWithConfig(ctx context.Context, transcript *MemoryTranscript, config TranscriptReaderConfig) TranscriptReader
```

## Usage Examples

### 1. Post-mortem Reading

```go
func readCompletedTranscript() {
    tr, err := terminal.OpenTranscript("session.log")
    if err != nil {
        log.Fatal(err)
    }
    defer tr.Close()

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
        fmt.Println(line)
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

    for {
        line, err := tr.NextLine(ctx)
        if err == io.EOF {
            break // Command completed
        }
        if err != nil {
            log.Printf("Error reading line: %v", err)
            break
        }
        fmt.Println("BUILD:", line)
    }
}
```

### 3. Unified Processing Function

```go
// This function works with both post-mortem and live readers
func processTranscript(tr terminal.TranscriptReader) {
    ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
    defer cancel()
    
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
        fmt.Printf("Line %d: %s\n", lineCount, line)
    }
    fmt.Printf("Total lines processed: %d\n", lineCount)
}

// Use with either mode:
// liveReader, _ := terminal.StreamTranscript(ctx, cmd)
// processTranscript(liveReader)
//
// fileReader, _ := terminal.OpenTranscript("session.log")
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

### 1. Go-Idiomatic Design
- **Simple method signatures**: `NextLine(ctx) (string, error)` follows the Go convention of returning data and error
- **Context support**: All reading operations accept `context.Context` for cancellation and timeouts
- **io.EOF semantics**: Uses standard Go EOF signaling for end-of-stream
- **Resource management**: `Close()` method for explicit cleanup

### 2. Unified API Surface
- **Single interface**: Both modes implement the same `TranscriptReader` interface
- **Factory functions**: Clear constructors for different modes (`OpenTranscript` vs `StreamTranscript`)
- **Consistent behavior**: Same error handling and cancellation semantics across modes

### 3. Buffering Strategy
- **Configurable buffer size**: Default 100 lines, adjustable per use case
- **Tolerable lag**: Default 1-second flush interval for live streams
- **Channel-based**: Uses Go channels for thread-safe buffering

### 4. Thread Safety
- **Concurrent access**: All implementations are thread-safe
- **Goroutine coordination**: Uses channels and mutexes appropriately
- **Context cancellation**: Respects context cancellation across all operations

### 5. Error Handling
- **Clear EOF signaling**: `io.EOF` when stream ends naturally
- **Context errors**: `context.Canceled` or `context.DeadlineExceeded` for timeouts
- **Scan errors**: Wraps underlying scanner errors with context

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

## Future Considerations

1. **Performance optimization**: Consider line pre-parsing for high-throughput scenarios
2. **Network streaming**: Could extend to support remote transcript sources
3. **Structured data**: Could add methods for accessing parsed metadata (timestamps, stream names)
4. **Tail-like functionality**: Could add options for following files like `tail -f`
