package terminal_test

import (
	"context"
	"fmt"
	"log"
	"os/exec"
	"strings"
	"time"

	"github.com/superfly/sprite-env/pkg/terminal"
)

// Example_postMortemReading demonstrates reading a completed transcript file.
func Example_postMortemReading() {
	// Open a completed transcript file
	tr, err := terminal.OpenTranscript("session.log")
	if err != nil {
		log.Fatal(err)
	}
	defer tr.Close()

	ctx := context.Background()
	for {
		line, err := tr.NextLine(ctx)
		if err != nil {
			break // io.EOF when complete
		}
		fmt.Println(line)
	}
}

// Example_liveStreaming demonstrates streaming output from a running command.
func Example_liveStreaming() {
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	cmd := exec.Command("echo", "Hello World")
	tr, err := terminal.StreamTranscript(ctx, cmd)
	if err != nil {
		log.Fatal(err)
	}
	defer tr.Close()

	for {
		line, err := tr.NextLine(ctx)
		if err != nil {
			break // io.EOF when command completes
		}
		fmt.Println(line)
	}
}

// Example_memoryTranscriptStreaming demonstrates streaming from a MemoryTranscript.
func Example_memoryTranscriptStreaming() {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	// Create and populate a memory transcript
	transcript := terminal.NewMemoryTranscript()
	stdoutWriter := transcript.StreamWriter("stdout")
	stdoutWriter.Write([]byte("Line 1\n"))
	stdoutWriter.Write([]byte("Line 2\n"))

	// Create a reader that will stream new content as it's added
	tr := terminal.StreamMemoryTranscript(ctx, transcript)
	defer tr.Close()

	// Read some lines
	for i := 0; i < 2; i++ {
		line, err := tr.NextLine(ctx)
		if err != nil {
			break
		}
		fmt.Println(line)
	}

	// Add more content to the transcript
	stdoutWriter.Write([]byte("Line 3\n"))

	// Wait a moment for the reader to pick up the new content
	time.Sleep(time.Second)

	// Continue reading
	line, err := tr.NextLine(ctx)
	if err == nil {
		fmt.Println(line)
	}
}

// Example_configuredReader demonstrates using custom configuration.
func Example_configuredReader() {
	ctx := context.Background()

	// Custom configuration for stderr-only reading with larger buffer
	config := terminal.TranscriptReaderConfig{
		BufferSize:    200,
		FlushInterval: 500 * time.Millisecond,
		Stream:        "stderr", // Only read stderr
	}

	cmd := exec.Command("sh", "-c", "echo 'stdout message'; echo 'stderr message' >&2")
	tr, err := terminal.StreamTranscriptWithConfig(ctx, cmd, config)
	if err != nil {
		log.Fatal(err)
	}
	defer tr.Close()

	for {
		line, err := tr.NextLine(ctx)
		if err != nil {
			break
		}
		fmt.Printf("STDERR: %s\n", line)
	}
}

// Example_timeoutHandling demonstrates timeout and cancellation handling.
func Example_timeoutHandling() {
	// Set a timeout for reading
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()

	// Long-running command that might take a while
	cmd := exec.Command("sleep", "10")
	tr, err := terminal.StreamTranscript(ctx, cmd)
	if err != nil {
		log.Fatal(err)
	}
	defer tr.Close()

	for {
		line, err := tr.NextLine(ctx)
		if err != nil {
			if err == context.DeadlineExceeded {
				fmt.Println("Reading timed out")
			} else {
				fmt.Printf("Error: %v\n", err)
			}
			break
		}
		fmt.Println(line)
	}
}

// Example_unifiedAPI demonstrates using the same code for both modes.
func Example_unifiedAPI() {
	// This function works with both post-mortem and live readers
	processTranscript := func(tr terminal.TranscriptReader) {
		ctx := context.Background()
		lineCount := 0

		for {
			line, err := tr.NextLine(ctx)
			if err != nil {
				break
			}
			lineCount++
			fmt.Printf("Line %d: %s\n", lineCount, line)
		}

		fmt.Printf("Total lines processed: %d\n", lineCount)
	}

	// Use with live streaming
	ctx := context.Background()
	cmd := exec.Command("echo", "Hello from live command")
	liveReader, err := terminal.StreamTranscript(ctx, cmd)
	if err == nil {
		fmt.Println("=== Live Streaming ===")
		processTranscript(liveReader)
		liveReader.Close()
	}

	// Use with post-mortem (if file exists)
	fileReader, err := terminal.OpenTranscript("session.log")
	if err == nil {
		fmt.Println("=== Post-mortem Reading ===")
		processTranscript(fileReader)
		fileReader.Close()
	}
}

// Example_terminalSessionIntegration shows integration with the existing Session API.
func Example_terminalSessionIntegration() {
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
	defer cancel()

	// Create a memory transcript to collect the session output
	transcript := terminal.NewMemoryTranscript()

	// Create and run a terminal session with transcript collection
	session := terminal.NewSession(
		terminal.WithCommand("echo", "Hello from session"),
		terminal.WithTTY(false),
		terminal.WithTranscript(transcript),
	)

	// Run the session in a goroutine
	go func() {
		stdin := strings.NewReader("")
		var stdout, stderr strings.Builder
		session.Run(ctx, stdin, &stdout, &stderr)
	}()

	// Stream the transcript as the session runs
	tr := terminal.StreamMemoryTranscript(ctx, transcript)
	defer tr.Close()

	// Small delay to let the session start
	time.Sleep(100 * time.Millisecond)

	for {
		line, err := tr.NextLine(ctx)
		if err != nil {
			break
		}
		fmt.Printf("Session output: %s\n", line)
	}
}
