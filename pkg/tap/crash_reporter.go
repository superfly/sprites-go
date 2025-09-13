// Package tap provides centralized logging and crash reporting functionality for the sprite-env application.
package tap

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"runtime/debug"
	"strings"
	"sync"
	"time"

	"github.com/aws/aws-sdk-go-v2/aws"
	"github.com/aws/aws-sdk-go-v2/config"
	"github.com/aws/aws-sdk-go-v2/credentials"
	"github.com/aws/aws-sdk-go-v2/service/s3"
)

// CrashReport represents a crash report for either the supervised process or Go runtime
type CrashReport struct {
	// Metadata
	ID        string    `json:"id"`
	Timestamp time.Time `json:"timestamp"`
	Hostname  string    `json:"hostname"`

	// Process information
	ProcessType string        `json:"process_type"` // "supervised" or "go_runtime"
	Command     string        `json:"command,omitempty"`
	Args        []string      `json:"args,omitempty"`
	ExitCode    int           `json:"exit_code,omitempty"`
	Signal      string        `json:"signal,omitempty"`
	Runtime     time.Duration `json:"runtime,omitempty"`

	// Crash details
	Error      string `json:"error,omitempty"`
	StackTrace string `json:"stack_trace,omitempty"`

	// System information
	Dmesg      string     `json:"dmesg,omitempty"`
	SystemInfo SystemInfo `json:"system_info"`

	// Process output (for supervised processes)
	RecentStdout string `json:"recent_stdout,omitempty"`
	RecentStderr string `json:"recent_stderr,omitempty"`
}

// SystemInfo contains system information at the time of crash
type SystemInfo struct {
	OS           string           `json:"os"`
	Arch         string           `json:"arch"`
	NumCPU       int              `json:"num_cpu"`
	GoVersion    string           `json:"go_version"`
	NumGoroutine int              `json:"num_goroutine"`
	MemStats     runtime.MemStats `json:"mem_stats,omitempty"`
}

// ToMap converts CrashReport to a map for admin channel events
func (cr *CrashReport) ToMap() map[string]interface{} {
	m := map[string]interface{}{
		"id":           cr.ID,
		"timestamp":    cr.Timestamp.Unix(),
		"hostname":     cr.Hostname,
		"process_type": cr.ProcessType,
	}

	if cr.Command != "" {
		m["command"] = cr.Command
	}
	if len(cr.Args) > 0 {
		m["args"] = cr.Args
	}
	if cr.ExitCode != 0 {
		m["exit_code"] = cr.ExitCode
	}
	if cr.Signal != "" {
		m["signal"] = cr.Signal
	}
	if cr.Runtime > 0 {
		m["runtime_seconds"] = cr.Runtime.Seconds()
	}
	if cr.Error != "" {
		m["error"] = cr.Error
	}
	if cr.StackTrace != "" {
		m["stack_trace"] = cr.StackTrace
	}

	return m
}

// S3Config contains S3 configuration for uploading crash reports
type S3Config struct {
	AccessKey   string
	SecretKey   string
	EndpointURL string
	Bucket      string
	Region      string
}

// CrashReporter handles crash report generation and storage
type CrashReporter struct {
	logger   *slog.Logger
	localDir string
	s3Config *S3Config
	s3Client *s3.Client
	mu       sync.Mutex
}

// NewCrashReporter creates a new crash reporter
func NewCrashReporter(logger *slog.Logger, localDir string, s3Config *S3Config) (*CrashReporter, error) {
	if logger == nil {
		logger = Default()
	}

	cr := &CrashReporter{
		logger:   logger,
		localDir: localDir,
		s3Config: s3Config,
	}

	// Create local crashes directory if it doesn't exist
	crashDir := filepath.Join(localDir, "crashes")
	if err := os.MkdirAll(crashDir, 0755); err != nil {
		return nil, fmt.Errorf("failed to create crash directory: %w", err)
	}

	// Initialize S3 client if configured
	if s3Config != nil && s3Config.AccessKey != "" && s3Config.SecretKey != "" {
		if err := cr.initS3Client(); err != nil {
			logger.Warn("Failed to initialize S3 client for crash reports", "error", err)
			// Don't fail, just disable S3 uploads
			cr.s3Config = nil
		}
	}

	return cr, nil
}

// initS3Client initializes the S3 client
func (cr *CrashReporter) initS3Client() error {
	region := cr.s3Config.Region
	if region == "" {
		region = "us-east-1"
	}

	cfg, err := config.LoadDefaultConfig(context.Background(),
		config.WithRegion(region),
		config.WithCredentialsProvider(credentials.NewStaticCredentialsProvider(
			cr.s3Config.AccessKey,
			cr.s3Config.SecretKey,
			"",
		)),
	)
	if err != nil {
		return fmt.Errorf("failed to load AWS config: %w", err)
	}

	cr.s3Client = s3.NewFromConfig(cfg, func(o *s3.Options) {
		if cr.s3Config.EndpointURL != "" {
			o.BaseEndpoint = aws.String(cr.s3Config.EndpointURL)
			o.UsePathStyle = true
		}
	})

	return nil
}

// ReportSupervisedProcessCrash reports a crash of the supervised process
func (cr *CrashReporter) ReportSupervisedProcessCrash(ctx context.Context, report *CrashReport) error {
	// Set fields that the crash reporter manages
	report.ID = cr.generateReportID(report.ExitCode, report.Runtime)
	report.Timestamp = time.Now().UTC()
	report.Hostname = getHostname()
	report.ProcessType = "supervised"

	// Collect system information
	cr.collectSystemInfo(report)

	// Try to get dmesg logs
	cr.collectDmesg(report)

	return cr.saveReport(ctx, report)
}

// ReportGoPanic reports a panic in the Go runtime
func (cr *CrashReporter) ReportGoPanic(ctx context.Context, report *CrashReport) error {
	// Set fields that the crash reporter manages
	report.ID = cr.generateReportID(report.ExitCode, 0)
	report.Timestamp = time.Now().UTC()
	report.Hostname = getHostname()
	report.ProcessType = "go_runtime"

	// Collect system information
	cr.collectSystemInfo(report)

	// Try to get dmesg logs
	cr.collectDmesg(report)

	return cr.saveReport(ctx, report)
}

// SetupPanicHandler sets up a global panic handler that reports crashes
func (cr *CrashReporter) SetupPanicHandler() {
	// Note: This should be called early in main() to ensure it catches all panics
	go func() {
		if r := recover(); r != nil {
			ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
			defer cancel()

			stackTrace := debug.Stack()

			cr.logger.Error("Go runtime panic", "panic", r, "stack", string(stackTrace))

			report := &CrashReport{
				ExitCode:   1,
				Error:      fmt.Sprintf("panic: %v", r),
				StackTrace: string(stackTrace),
			}

			if err := cr.ReportGoPanic(ctx, report); err != nil {
				cr.logger.Error("Failed to report panic", "error", err)
			}

			// Re-panic to maintain normal panic behavior
			panic(r)
		}
	}()
}

// collectSystemInfo collects system information
func (cr *CrashReporter) collectSystemInfo(report *CrashReport) {
	report.SystemInfo = SystemInfo{
		OS:     runtime.GOOS,
		Arch:   runtime.GOARCH,
		NumCPU: runtime.NumCPU(),
	}

	// Only collect Go runtime specific info for Go runtime crashes
	if report.ProcessType == "go_runtime" {
		report.SystemInfo.GoVersion = runtime.Version()
		report.SystemInfo.NumGoroutine = runtime.NumGoroutine()
		runtime.ReadMemStats(&report.SystemInfo.MemStats)
	}
}

// collectDmesg attempts to collect recent dmesg logs
func (cr *CrashReporter) collectDmesg(report *CrashReport) {
	// Get dmesg from the last 60 seconds
	// Use --since to filter by time (requires util-linux 2.22+)
	cmd := exec.Command("dmesg", "-T", "--decode", "--since", "-60s")
	output, err := cmd.Output()
	if err != nil {
		// Fallback to getting last 50 lines if --since is not supported
		cmd = exec.Command("dmesg", "-T", "--decode")
		output, err = cmd.Output()
		if err != nil {
			cr.logger.Debug("Failed to collect dmesg logs", "error", err)
			return
		}

		// Filter by timestamp manually if --since failed
		lines := strings.Split(string(output), "\n")
		cutoff := time.Now().Add(-60 * time.Second)
		var recentLines []string

		for i := len(lines) - 1; i >= 0; i-- {
			line := lines[i]
			if line == "" {
				continue
			}

			// Try to parse timestamp from dmesg -T format
			// Format: [Mon Jan  2 15:04:05 2006] message
			if len(line) > 28 && line[0] == '[' {
				if idx := strings.Index(line, "]"); idx > 0 {
					timeStr := line[1:idx]
					if t, err := time.Parse("Mon Jan  2 15:04:05 2006", timeStr); err == nil {
						if t.Before(cutoff) {
							break
						}
					}
				}
			}
			recentLines = append([]string{line}, recentLines...)
		}

		report.Dmesg = strings.Join(recentLines, "\n")
		return
	}

	report.Dmesg = string(output)
}

// generateReportID generates a unique report ID that includes timestamp, exit code, and runtime
func (cr *CrashReporter) generateReportID(exitCode int, runtime time.Duration) string {
	timestamp := time.Now().UTC().Format("20060102-150405")
	runtimeMs := int(runtime.Milliseconds())

	// Format: timestamp-exitcode-runtime_ms-random
	// This ensures lexical sorting by timestamp
	return fmt.Sprintf("%s-exit%d-runtime%dms-%d",
		timestamp,
		exitCode,
		runtimeMs,
		time.Now().UnixNano()%10000,
	)
}

// saveReport saves the crash report to disk and optionally uploads to S3
func (cr *CrashReporter) saveReport(ctx context.Context, report *CrashReport) error {
	cr.mu.Lock()
	defer cr.mu.Unlock()

	// Marshal report to JSON
	data, err := json.MarshalIndent(report, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal crash report: %w", err)
	}

	// Save to local disk
	filename := fmt.Sprintf("%s.json", report.ID)
	localPath := filepath.Join(cr.localDir, "crashes", filename)

	if err := os.WriteFile(localPath, data, 0644); err != nil {
		return fmt.Errorf("failed to write crash report to disk: %w", err)
	}

	cr.logger.Info("Crash report saved to disk", "path", localPath, "id", report.ID)

	// Try to upload to S3 if configured
	if cr.s3Client != nil && cr.s3Config != nil {
		s3Key := fmt.Sprintf("crashes/%s", filename)

		_, err := cr.s3Client.PutObject(ctx, &s3.PutObjectInput{
			Bucket:      aws.String(cr.s3Config.Bucket),
			Key:         aws.String(s3Key),
			Body:        bytes.NewReader(data),
			ContentType: aws.String("application/json"),
		})

		if err != nil {
			cr.logger.Error("Failed to upload crash report to S3", "error", err, "key", s3Key)
			// Don't fail the whole operation if S3 upload fails
		} else {
			cr.logger.Info("Crash report uploaded to S3", "bucket", cr.s3Config.Bucket, "key", s3Key)
		}
	}

	return nil
}

// getHostname returns the hostname or a default value
func getHostname() string {
	hostname, err := os.Hostname()
	if err != nil {
		return "unknown"
	}
	return hostname
}

// CircularBuffer is a thread-safe circular buffer for capturing recent output
type CircularBuffer struct {
	mu       sync.Mutex
	buffer   []byte
	size     int
	writePos int
	full     bool
}

// NewCircularBuffer creates a new circular buffer of the specified size
func NewCircularBuffer(size int) *CircularBuffer {
	return &CircularBuffer{
		buffer: make([]byte, size),
		size:   size,
	}
}

// Write implements io.Writer
func (cb *CircularBuffer) Write(p []byte) (n int, err error) {
	cb.mu.Lock()
	defer cb.mu.Unlock()

	n = len(p)
	for i := 0; i < n; i++ {
		cb.buffer[cb.writePos] = p[i]
		cb.writePos = (cb.writePos + 1) % cb.size
		if cb.writePos == 0 {
			cb.full = true
		}
	}

	return n, nil
}

// GetContents returns the current contents of the buffer
func (cb *CircularBuffer) GetContents() string {
	cb.mu.Lock()
	defer cb.mu.Unlock()

	if !cb.full && cb.writePos == 0 {
		return ""
	}

	if cb.full {
		// Buffer has wrapped around
		result := make([]byte, cb.size)
		copy(result, cb.buffer[cb.writePos:])
		copy(result[cb.size-cb.writePos:], cb.buffer[:cb.writePos])
		return string(result)
	}

	// Buffer hasn't wrapped yet
	return string(cb.buffer[:cb.writePos])
}

// TeeCircularBuffer creates a writer that writes to both the original writer and a circular buffer
func TeeCircularBuffer(w io.Writer, size int) (io.Writer, *CircularBuffer) {
	cb := NewCircularBuffer(size)
	return io.MultiWriter(w, cb), cb
}
