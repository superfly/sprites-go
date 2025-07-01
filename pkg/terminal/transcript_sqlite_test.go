package terminal

import (
	"context"
	"fmt"
	"log/slog"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func TestSQLiteTranscript_NewAndClose(t *testing.T) {
	// Create temporary directory for test database
	tmpDir := t.TempDir()
	dbPath := filepath.Join(tmpDir, "test_transcript.db")

	config := SQLiteTranscriptConfig{
		DBPath: dbPath,
		TTY:    false,
		Logger: slog.Default(),
	}

	// Create SQLite transcript
	transcript, err := NewSQLiteTranscript(config)
	if err != nil {
		t.Fatalf("Failed to create SQLite transcript: %v", err)
	}

	// Verify database file was created
	if _, err := os.Stat(dbPath); os.IsNotExist(err) {
		t.Errorf("Database file was not created: %s", dbPath)
	}

	// Close transcript
	if err := transcript.Close(); err != nil {
		t.Errorf("Failed to close transcript: %v", err)
	}
}

func TestSQLiteTranscript_StreamWriting(t *testing.T) {
	// Create temporary directory for test database
	tmpDir := t.TempDir()
	dbPath := filepath.Join(tmpDir, "test_transcript.db")

	env := []string{"TEST_VAR=test_value"}

	config := SQLiteTranscriptConfig{
		DBPath: dbPath,
		Env:    env,
		TTY:    true,
		Logger: slog.Default(),
	}

	// Create SQLite transcript
	transcript, err := NewSQLiteTranscript(config)
	if err != nil {
		t.Fatalf("Failed to create SQLite transcript: %v", err)
	}
	defer transcript.Close()

	// Test writing to stdout stream
	stdoutWriter := transcript.StreamWriter("stdout")
	testMessages := []string{
		"Hello, world!\n",
		"This is a test message\n",
		"Another line of output\n",
	}

	for _, msg := range testMessages {
		n, err := stdoutWriter.Write([]byte(msg))
		if err != nil {
			t.Errorf("Failed to write to stdout stream: %v", err)
		}
		if n != len(msg) {
			t.Errorf("Expected to write %d bytes, wrote %d", len(msg), n)
		}
	}

	// Test writing to stderr stream
	stderrWriter := transcript.StreamWriter("stderr")
	errorMsg := "Error: something went wrong\n"
	if _, err := stderrWriter.Write([]byte(errorMsg)); err != nil {
		t.Errorf("Failed to write to stderr stream: %v", err)
	}

	// Test writing to stdin stream
	stdinWriter := transcript.StreamWriter("stdin")
	inputMsg := "user input\n"
	if _, err := stdinWriter.Write([]byte(inputMsg)); err != nil {
		t.Errorf("Failed to write to stdin stream: %v", err)
	}

	// Set exit code
	if err := transcript.SetExitCode(0); err != nil {
		t.Errorf("Failed to set exit code: %v", err)
	}

	// Get session ID for verification
	sessionID := transcript.GetSessionID()
	if sessionID == "" {
		t.Error("Session ID should not be empty")
	}

	// Close transcript to ensure all data is written
	if err := transcript.Close(); err != nil {
		t.Errorf("Failed to close transcript: %v", err)
	}

	// Now read back the data using the backend
	backend, err := NewSQLiteTranscriptBackend(dbPath)
	if err != nil {
		t.Fatalf("Failed to create SQLite backend: %v", err)
	}
	defer backend.Close()

	// Test reading session info
	sqliteBackend := backend.(*sqliteTranscriptBackend)
	sessionInfo, err := sqliteBackend.GetSessionInfo(context.Background(), sessionID)
	if err != nil {
		t.Errorf("Failed to get session info: %v", err)
	} else {
		if sessionInfo.WorkingDir != "/tmp" {
			t.Errorf("Expected working dir '/tmp', got '%s'", sessionInfo.WorkingDir)
		}
		if !sessionInfo.TTY {
			t.Error("Expected TTY to be true")
		}
	}

	// Test reading log lines
	query := LineQuery{
		SessionID: sessionID,
		Stream:    "all",
		Limit:     100,
	}

	lines, err := backend.GetLines(context.Background(), query)
	if err != nil {
		t.Errorf("Failed to get lines: %v", err)
	}

	// Verify we got the expected number of lines (3 stdout + 1 stderr + 1 stdin)
	expectedLineCount := 5
	if len(lines) != expectedLineCount {
		t.Errorf("Expected %d lines, got %d", expectedLineCount, len(lines))
	}

	// Verify line content
	for _, line := range lines {
		if line.SessionID != sessionID {
			t.Errorf("Expected session ID %s, got %s", sessionID, line.SessionID)
		}
		if line.Sequence <= 0 {
			t.Errorf("Expected positive sequence number, got %d", line.Sequence)
		}
		if line.Text == "" {
			t.Error("Expected non-empty text")
		}
	}
}

func TestSQLiteTranscript_StreamFiltering(t *testing.T) {
	// Create temporary directory for test database
	tmpDir := t.TempDir()
	dbPath := filepath.Join(tmpDir, "test_transcript.db")

	config := SQLiteTranscriptConfig{
		DBPath: dbPath,
		TTY:    false,
		Logger: slog.Default(),
	}

	// Create SQLite transcript
	transcript, err := NewSQLiteTranscript(config)
	if err != nil {
		t.Fatalf("Failed to create SQLite transcript: %v", err)
	}
	defer transcript.Close()

	// Write to different streams
	stdoutWriter := transcript.StreamWriter("stdout")
	stderrWriter := transcript.StreamWriter("stderr")
	stdinWriter := transcript.StreamWriter("stdin")

	stdoutWriter.Write([]byte("stdout message 1\n"))
	stdoutWriter.Write([]byte("stdout message 2\n"))
	stderrWriter.Write([]byte("stderr message 1\n"))
	stdinWriter.Write([]byte("stdin message 1\n"))

	sessionID := transcript.GetSessionID()

	// Close transcript to ensure all data is written
	transcript.Close()

	// Create backend for reading
	backend, err := NewSQLiteTranscriptBackend(dbPath)
	if err != nil {
		t.Fatalf("Failed to create SQLite backend: %v", err)
	}
	defer backend.Close()

	// Test filtering by stdout stream
	stdoutQuery := LineQuery{
		SessionID: sessionID,
		Stream:    "stdout",
		Limit:     100,
	}
	stdoutLines, err := backend.GetLines(context.Background(), stdoutQuery)
	if err != nil {
		t.Errorf("Failed to get stdout lines: %v", err)
	}
	if len(stdoutLines) != 2 {
		t.Errorf("Expected 2 stdout lines, got %d", len(stdoutLines))
	}
	for _, line := range stdoutLines {
		if line.Stream != "stdout" {
			t.Errorf("Expected stdout stream, got %s", line.Stream)
		}
		if !strings.Contains(line.Text, "stdout") {
			t.Errorf("Expected stdout message, got %s", line.Text)
		}
	}

	// Test filtering by stderr stream
	stderrQuery := LineQuery{
		SessionID: sessionID,
		Stream:    "stderr",
		Limit:     100,
	}
	stderrLines, err := backend.GetLines(context.Background(), stderrQuery)
	if err != nil {
		t.Errorf("Failed to get stderr lines: %v", err)
	}
	if len(stderrLines) != 1 {
		t.Errorf("Expected 1 stderr line, got %d", len(stderrLines))
	}
	if len(stderrLines) > 0 && stderrLines[0].Stream != "stderr" {
		t.Errorf("Expected stderr stream, got %s", stderrLines[0].Stream)
	}

	// Test getting all streams
	allQuery := LineQuery{
		SessionID: sessionID,
		Stream:    "all",
		Limit:     100,
	}
	allLines, err := backend.GetLines(context.Background(), allQuery)
	if err != nil {
		t.Errorf("Failed to get all lines: %v", err)
	}
	if len(allLines) != 4 {
		t.Errorf("Expected 4 total lines, got %d", len(allLines))
	}
}

func TestSQLiteTranscript_SequenceOrdering(t *testing.T) {
	// Create temporary directory for test database
	tmpDir := t.TempDir()
	dbPath := filepath.Join(tmpDir, "test_transcript.db")

	config := SQLiteTranscriptConfig{
		DBPath: dbPath,
		TTY:    false,
		Logger: slog.Default(),
	}

	// Create SQLite transcript
	transcript, err := NewSQLiteTranscript(config)
	if err != nil {
		t.Fatalf("Failed to create SQLite transcript: %v", err)
	}
	defer transcript.Close()

	// Write multiple messages in order
	stdoutWriter := transcript.StreamWriter("stdout")
	for i := 1; i <= 5; i++ {
		msg := fmt.Sprintf("Message %d\n", i)
		stdoutWriter.Write([]byte(msg))
		// Small delay to ensure different timestamps
		time.Sleep(time.Millisecond)
	}

	sessionID := transcript.GetSessionID()
	transcript.Close()

	// Create backend for reading
	backend, err := NewSQLiteTranscriptBackend(dbPath)
	if err != nil {
		t.Fatalf("Failed to create SQLite backend: %v", err)
	}
	defer backend.Close()

	// Get all lines
	query := LineQuery{
		SessionID: sessionID,
		Stream:    "stdout",
		Limit:     100,
	}
	lines, err := backend.GetLines(context.Background(), query)
	if err != nil {
		t.Errorf("Failed to get lines: %v", err)
	}

	if len(lines) != 5 {
		t.Errorf("Expected 5 lines, got %d", len(lines))
	}

	// Verify sequence ordering
	for i, line := range lines {
		expectedSequence := int64(i + 1)
		if line.Sequence != expectedSequence {
			t.Errorf("Expected sequence %d, got %d", expectedSequence, line.Sequence)
		}
		expectedText := fmt.Sprintf("Message %d", i+1)
		if !strings.Contains(line.Text, expectedText) {
			t.Errorf("Expected text to contain '%s', got '%s'", expectedText, line.Text)
		}
	}

	// Test AfterSequence filtering
	afterQuery := LineQuery{
		SessionID:     sessionID,
		AfterSequence: 3,
		Stream:        "stdout",
		Limit:         100,
	}
	afterLines, err := backend.GetLines(context.Background(), afterQuery)
	if err != nil {
		t.Errorf("Failed to get lines after sequence 3: %v", err)
	}

	if len(afterLines) != 2 {
		t.Errorf("Expected 2 lines after sequence 3, got %d", len(afterLines))
	}

	for _, line := range afterLines {
		if line.Sequence <= 3 {
			t.Errorf("Expected sequence > 3, got %d", line.Sequence)
		}
	}
}

func TestSQLiteTranscript_ListSessions(t *testing.T) {
	// Create temporary directory for test database
	tmpDir := t.TempDir()
	dbPath := filepath.Join(tmpDir, "test_transcript.db")

	// Create multiple sessions
	sessionIDs := []string{}
	for i := 1; i <= 3; i++ {
		config := SQLiteTranscriptConfig{
			DBPath: dbPath,
			TTY:    i%2 == 0, // Alternate TTY setting
			Logger: slog.Default(),
		}

		transcript, err := NewSQLiteTranscript(config)
		if err != nil {
			t.Fatalf("Failed to create SQLite transcript %d: %v", i, err)
		}

		sessionIDs = append(sessionIDs, transcript.GetSessionID())
		transcript.SetExitCode(i) // Different exit codes
		transcript.Close()

		// Small delay to ensure different timestamps
		time.Sleep(time.Millisecond * 10)
	}

	// Create backend for reading
	backend, err := NewSQLiteTranscriptBackend(dbPath)
	if err != nil {
		t.Fatalf("Failed to create SQLite backend: %v", err)
	}
	defer backend.Close()

	sqliteBackend := backend.(*sqliteTranscriptBackend)

	// Test listing all sessions
	sessions, err := sqliteBackend.ListSessions(context.Background(), 0, 0)
	if err != nil {
		t.Errorf("Failed to list sessions: %v", err)
	}

	if len(sessions) != 3 {
		t.Errorf("Expected 3 sessions, got %d", len(sessions))
	}

	// Verify sessions are ordered by start_time DESC (most recent first)
	for i, session := range sessions {
		expectedExitCode := 3 - i // Reverse order
		if session.ExitCode != expectedExitCode {
			t.Errorf("Expected exit code %d, got %d", expectedExitCode, session.ExitCode)
		}
	}

	// Test limiting sessions
	limitedSessions, err := sqliteBackend.ListSessions(context.Background(), 2, 0)
	if err != nil {
		t.Errorf("Failed to list limited sessions: %v", err)
	}

	if len(limitedSessions) != 2 {
		t.Errorf("Expected 2 limited sessions, got %d", len(limitedSessions))
	}

	// Test with offset
	offsetSessions, err := sqliteBackend.ListSessions(context.Background(), 2, 1)
	if err != nil {
		t.Errorf("Failed to list offset sessions: %v", err)
	}

	if len(offsetSessions) != 2 {
		t.Errorf("Expected 2 offset sessions, got %d", len(offsetSessions))
	}
}

func TestSQLiteTranscript_ErrorHandling(t *testing.T) {
	// Test with invalid database path
	invalidConfig := SQLiteTranscriptConfig{
		DBPath: "/invalid/path/that/does/not/exist/test.db",
		Logger: slog.Default(),
	}

	_, err := NewSQLiteTranscript(invalidConfig)
	if err == nil {
		t.Error("Expected error for invalid database path, got nil")
	}

	// Test backend with non-existent database
	_, err = NewSQLiteTranscriptBackend("/non/existent/path/test.db")
	if err == nil {
		t.Error("Expected error for non-existent database, got nil")
	}
}

func TestSQLiteTranscript_ConcurrentWrites(t *testing.T) {
	// Create temporary directory for test database
	tmpDir := t.TempDir()
	dbPath := filepath.Join(tmpDir, "test_transcript.db")

	config := SQLiteTranscriptConfig{
		DBPath: dbPath,
		TTY:    false,
		Logger: slog.Default(),
	}

	// Create SQLite transcript
	transcript, err := NewSQLiteTranscript(config)
	if err != nil {
		t.Fatalf("Failed to create SQLite transcript: %v", err)
	}
	defer transcript.Close()

	// Get writers for different streams
	stdoutWriter := transcript.StreamWriter("stdout")
	stderrWriter := transcript.StreamWriter("stderr")

	// Write concurrently from multiple goroutines
	done := make(chan bool, 2)

	go func() {
		for i := 0; i < 10; i++ {
			msg := fmt.Sprintf("stdout message %d\n", i)
			stdoutWriter.Write([]byte(msg))
			time.Sleep(time.Millisecond)
		}
		done <- true
	}()

	go func() {
		for i := 0; i < 10; i++ {
			msg := fmt.Sprintf("stderr message %d\n", i)
			stderrWriter.Write([]byte(msg))
			time.Sleep(time.Millisecond)
		}
		done <- true
	}()

	// Wait for both goroutines to complete
	<-done
	<-done

	sessionID := transcript.GetSessionID()
	transcript.Close()

	// Verify all messages were written
	backend, err := NewSQLiteTranscriptBackend(dbPath)
	if err != nil {
		t.Fatalf("Failed to create SQLite backend: %v", err)
	}
	defer backend.Close()

	query := LineQuery{
		SessionID: sessionID,
		Stream:    "all",
		Limit:     100,
	}
	lines, err := backend.GetLines(context.Background(), query)
	if err != nil {
		t.Errorf("Failed to get lines: %v", err)
	}

	if len(lines) != 20 {
		t.Errorf("Expected 20 lines (10 stdout + 10 stderr), got %d", len(lines))
	}

	// Count stdout and stderr lines
	stdoutCount := 0
	stderrCount := 0
	for _, line := range lines {
		if line.Stream == "stdout" {
			stdoutCount++
		} else if line.Stream == "stderr" {
			stderrCount++
		}
	}

	if stdoutCount != 10 {
		t.Errorf("Expected 10 stdout lines, got %d", stdoutCount)
	}
	if stderrCount != 10 {
		t.Errorf("Expected 10 stderr lines, got %d", stderrCount)
	}
}
