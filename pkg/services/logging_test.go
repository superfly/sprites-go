package services

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func TestServiceLogging(t *testing.T) {
	// Create temporary directory for test
	tmpDir, err := os.MkdirTemp("", "services-logging-test-*")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	// Create log directory
	logDir := filepath.Join(tmpDir, "log")

	// Create manager with logging
	manager, err := NewManager(tmpDir, WithLogDir(logDir))
	if err != nil {
		t.Fatal(err)
	}
	defer manager.Close()

	// Start the manager
	if err := manager.Start(); err != nil {
		t.Fatal(err)
	}
	// Create a service that outputs to stdout and stderr
	svc := &Service{
		Name: "log-test",
		Cmd:  "bash",
		Args: []string{"-c", `echo "stdout line 1" && echo "stderr line 1" >&2 && echo "stdout line 2" && echo "stderr line 2" >&2`},
	}
	if err := manager.CreateService(svc); err != nil {
		t.Fatal(err)
	}

	// Start the service
	if err := manager.StartService("log-test"); err != nil {
		t.Fatal(err)
	}

	// Wait for service to complete
	time.Sleep(200 * time.Millisecond)

	// Check that log files were created
	stdoutPath := filepath.Join(logDir, "services", "log-test.log")
	stderrPath := filepath.Join(logDir, "services", "log-test.stderr.log")

	// Check stdout log
	stdoutData, err := os.ReadFile(stdoutPath)
	if err != nil {
		t.Errorf("Failed to read stdout log: %v", err)
	} else {
		content := string(stdoutData)
		if !strings.Contains(content, "stdout line 1") || !strings.Contains(content, "stdout line 2") {
			t.Errorf("stdout log missing expected content: %s", content)
		}
	}

	// Check stderr log
	stderrData, err := os.ReadFile(stderrPath)
	if err != nil {
		t.Errorf("Failed to read stderr log: %v", err)
	} else {
		content := string(stderrData)
		if !strings.Contains(content, "stderr line 1") || !strings.Contains(content, "stderr line 2") {
			t.Errorf("stderr log missing expected content: %s", content)
		}
	}
}

func TestLogFileTruncation(t *testing.T) {
	// Create temporary directory for test
	tmpDir, err := os.MkdirTemp("", "services-truncate-test-*")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	// Create log directory
	logDir := filepath.Join(tmpDir, "log")
	if err := os.MkdirAll(filepath.Join(logDir, "services"), 0755); err != nil {
		t.Fatal(err)
	}

	// Create a large log file (>1MB)
	largePath := filepath.Join(logDir, "services", "large-test.log")
	largeFile, err := os.Create(largePath)
	if err != nil {
		t.Fatal(err)
	}

	// Write 2MB of data
	data := make([]byte, 2*1024*1024)
	for i := range data {
		data[i] = 'X'
	}
	if _, err := largeFile.Write(data); err != nil {
		t.Fatal(err)
	}
	largeFile.Close()

	// Verify file is large
	info, err := os.Stat(largePath)
	if err != nil {
		t.Fatal(err)
	}
	if info.Size() <= 1024*1024 {
		t.Error("Expected file to be > 1MB")
	}

	// Now create a service that will use this log file
	manager, err := NewManager(tmpDir, WithLogDir(logDir))
	if err != nil {
		t.Fatal(err)
	}
	defer manager.Close()

	// Start the manager
	if err := manager.Start(); err != nil {
		t.Fatal(err)
	}
	svc := &Service{
		Name: "large-test",
		Cmd:  "echo",
		Args: []string{"new content"},
	}
	if err := manager.CreateService(svc); err != nil {
		t.Fatal(err)
	}

	// Start the service
	if err := manager.StartService("large-test"); err != nil {
		t.Fatal(err)
	}

	// Wait for service to complete
	time.Sleep(100 * time.Millisecond)

	// Check that file was truncated
	info, err = os.Stat(largePath)
	if err != nil {
		t.Fatal(err)
	}
	if info.Size() > 1024*1024 {
		t.Errorf("Expected file to be truncated, but size is %d", info.Size())
	}

	// Verify new content is there
	content, err := os.ReadFile(largePath)
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(string(content), "new content") {
		t.Error("Expected new content in truncated file")
	}
	if strings.Contains(string(content), "XXXX") {
		t.Error("Old content should have been truncated")
	}
}
