package tap

import (
	"context"
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func TestCrashReporter(t *testing.T) {
	// Create a temporary directory for test
	tmpDir, err := os.MkdirTemp("", "crash-reporter-test-*")
	if err != nil {
		t.Fatalf("Failed to create temp dir: %v", err)
	}
	defer os.RemoveAll(tmpDir)

	// Create crash reporter without S3 (local only)
	logger := NewDiscardLogger() // Use discard logger for tests
	cr, err := NewCrashReporter(logger, tmpDir, nil)
	if err != nil {
		t.Fatalf("Failed to create crash reporter: %v", err)
	}

	t.Run("SupervisedProcessCrash", func(t *testing.T) {
		ctx := context.Background()

		// Report a crash
		err := cr.ReportSupervisedProcessCrash(ctx, &CrashReport{
			ProcessType:  "supervised",
			Command:      "/bin/test-app",
			Args:         []string{"--crash"},
			ExitCode:     42,
			Signal:       "",
			Runtime:      5 * time.Minute,
			RecentStdout: "Last stdout line\n",
			RecentStderr: "Error: crash!\n",
		})

		if err != nil {
			t.Fatalf("Failed to report crash: %v", err)
		}

		// Verify crash report was written
		crashDir := filepath.Join(tmpDir, "crashes")
		files, err := os.ReadDir(crashDir)
		if err != nil {
			t.Fatalf("Failed to read crash dir: %v", err)
		}

		if len(files) != 1 {
			t.Fatalf("Expected 1 crash report, found %d", len(files))
		}

		// Read and verify the crash report
		reportPath := filepath.Join(crashDir, files[0].Name())
		data, err := os.ReadFile(reportPath)
		if err != nil {
			t.Fatalf("Failed to read crash report: %v", err)
		}

		var report CrashReport
		if err := json.Unmarshal(data, &report); err != nil {
			t.Fatalf("Failed to unmarshal crash report: %v", err)
		}

		// Verify report contents
		if report.ProcessType != "supervised" {
			t.Errorf("Expected process type 'supervised', got %s", report.ProcessType)
		}
		if report.Command != "/bin/test-app" {
			t.Errorf("Expected command '/bin/test-app', got %s", report.Command)
		}
		if report.ExitCode != 42 {
			t.Errorf("Expected exit code 42, got %d", report.ExitCode)
		}
		if report.Runtime != 5*time.Minute {
			t.Errorf("Expected runtime 5m, got %v", report.Runtime)
		}
		if report.RecentStdout != "Last stdout line\n" {
			t.Errorf("Expected stdout 'Last stdout line\\n', got %s", report.RecentStdout)
		}
		if report.RecentStderr != "Error: crash!\n" {
			t.Errorf("Expected stderr 'Error: crash!\\n', got %s", report.RecentStderr)
		}

		// Verify filename format
		filename := files[0].Name()
		if !strings.Contains(filename, "exit42") {
			t.Errorf("Expected filename to contain 'exit42', got %s", filename)
		}
		if !strings.Contains(filename, "runtime300000ms") {
			t.Errorf("Expected filename to contain 'runtime300000ms', got %s", filename)
		}
	})

	t.Run("GoPanic", func(t *testing.T) {
		ctx := context.Background()

		// Report a panic
		err := cr.ReportGoPanic(ctx, &CrashReport{
			ProcessType: "go_runtime",
			Error:       "test panic",
			StackTrace:  "goroutine 1 [running]:\nmain.main()\n\t/test/main.go:10 +0x123",
		})
		if err != nil {
			t.Fatalf("Failed to report panic: %v", err)
		}

		// Verify crash report was written
		crashDir := filepath.Join(tmpDir, "crashes")
		files, err := os.ReadDir(crashDir)
		if err != nil {
			t.Fatalf("Failed to read crash dir: %v", err)
		}

		// Should now have 2 files
		if len(files) != 2 {
			t.Fatalf("Expected 2 crash reports, found %d", len(files))
		}
	})
}

func TestCircularBuffer(t *testing.T) {
	t.Run("BasicWrite", func(t *testing.T) {
		cb := NewCircularBuffer(10)

		n, err := cb.Write([]byte("hello"))
		if err != nil {
			t.Fatalf("Write failed: %v", err)
		}
		if n != 5 {
			t.Errorf("Expected 5 bytes written, got %d", n)
		}

		contents := cb.GetContents()
		if contents != "hello" {
			t.Errorf("Expected 'hello', got '%s'", contents)
		}
	})

	t.Run("Wraparound", func(t *testing.T) {
		cb := NewCircularBuffer(5)

		// Write more than buffer size
		cb.Write([]byte("12345"))
		cb.Write([]byte("67890"))

		contents := cb.GetContents()
		if contents != "67890" {
			t.Errorf("Expected '67890' after wraparound, got '%s'", contents)
		}
	})

	t.Run("PartialWraparound", func(t *testing.T) {
		cb := NewCircularBuffer(8)

		cb.Write([]byte("12345"))
		cb.Write([]byte("6789"))

		contents := cb.GetContents()
		// Should contain "23456789" (wrapped, starting from position 1)
		if contents != "23456789" {
			t.Errorf("Expected '23456789', got '%s'", contents)
		}
	})
}
