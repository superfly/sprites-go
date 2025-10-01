package juicefs

import (
	"bytes"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

func parseJSONLinesIntegration(t *testing.T, data string) []map[string]any {
	lines := strings.Split(strings.TrimSpace(data), "\n")
	var out []map[string]any
	for _, l := range lines {
		l = strings.TrimSpace(l)
		if l == "" {
			continue
		}
		var m map[string]any
		if err := json.Unmarshal([]byte(l), &m); err != nil {
			t.Fatalf("failed to parse JSON line %q: %v", l, err)
		}
		out = append(out, m)
	}
	return out
}

func isMountReadyPath(mountPath string) bool {
	if _, err := os.Stat(mountPath); err != nil {
		return false
	}
	b, err := os.ReadFile("/proc/mounts")
	if err != nil {
		return false
	}
	return strings.Contains(string(b), mountPath)
}

func TestJuiceFSRealProcessStructuredLogs(t *testing.T) {
	if os.Getenv("SPRITE_TEST_DOCKER") != "1" {
		t.Skip("requires Docker test container with juicefs binary")
	}

	// Just run a simple juicefs command that will output structured logs
	// We don't need to actually mount anything - we're just testing log parsing
	baseDir := t.TempDir()
	metaDB := filepath.Join(baseDir, "metadata.db")
	metaURL := fmt.Sprintf("sqlite3://%s", metaDB)
	localBucket := filepath.Join(baseDir, "local")
	_ = os.MkdirAll(localBucket, 0755)

	// Run format command which outputs structured logs without needing FUSE
	cmd := exec.Command("juicefs", "format",
		"--storage", "file",
		"--bucket", localBucket,
		"--trash-days", "1",
		metaURL,
		"testvol",
	)
	cmd.Env = append(os.Environ(), "JUICEFS_LOG_FORMAT=json")

	stdout, err := cmd.StdoutPipe()
	if err != nil {
		t.Fatalf("stdout pipe: %v", err)
	}
	stderr, err := cmd.StderrPipe()
	if err != nil {
		t.Fatalf("stderr pipe: %v", err)
	}

	var buf bytes.Buffer
	logger := slog.New(slog.NewTextHandler(io.Discard, &slog.HandlerOptions{Level: slog.LevelDebug}))
	w := NewOutputWatcher(logger, "/fake/path", &buf)
	w.Watch(stdout, stderr)

	if err := cmd.Start(); err != nil {
		t.Fatalf("start command: %v", err)
	}

	// Wait for command to complete
	if err := cmd.Wait(); err != nil {
		// It's okay if the command errors - we just need some output
		t.Logf("command exited with error (expected): %v", err)
	}

	// Give goroutines a moment to finish processing output
	time.Sleep(100 * time.Millisecond)

	// Validate we captured structured JSON lines
	records := parseJSONLinesIntegration(t, buf.String())
	if len(records) == 0 {
		t.Fatalf("expected structured logs from juicefs, got none. output:\n%s", buf.String())
	}

	// Ensure some lines have proper structure (level and msg fields at minimum)
	valid := false
	for _, r := range records {
		// Check for structured log fields - should have level and some content
		if (r["level"] == "info" || r["level"] == "error" || r["level"] == "debug") && r["msg"] != nil {
			valid = true
			break
		}
	}
	if !valid {
		t.Fatalf("no valid structured juicefs records found: %s", buf.String())
	}

	t.Logf("Successfully parsed %d structured log records", len(records))
}
