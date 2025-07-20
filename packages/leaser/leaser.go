package leaser

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/aws/aws-sdk-go-v2/aws"
	"github.com/aws/aws-sdk-go-v2/credentials"
	"github.com/aws/aws-sdk-go-v2/service/s3"
	"github.com/aws/smithy-go/middleware"
	smithyhttp "github.com/aws/smithy-go/transport/http"
)

// S3API interface for S3 operations used by Leaser
type S3API interface {
	PutObject(ctx context.Context, params *s3.PutObjectInput, optFns ...func(*s3.Options)) (*s3.PutObjectOutput, error)
	GetObject(ctx context.Context, params *s3.GetObjectInput, optFns ...func(*s3.Options)) (*s3.GetObjectOutput, error)
	HeadObject(ctx context.Context, params *s3.HeadObjectInput, optFns ...func(*s3.Options)) (*s3.HeadObjectOutput, error)
}

// Leaser handles distributed leasing using S3 optimistic concurrency
type Leaser struct {
	s3Client      S3API
	bucketName    string
	primaryRegion string
	machineID     string
	leaseKey      string
	etagFilePath  string
	baseDir       string
	attemptCount  int
	refreshTicker *time.Ticker
	stopCh        chan struct{}
	stoppedCh     chan struct{}
	currentETag   string
	logger        *slog.Logger
}

// Config holds the configuration for the Leaser
type Config struct {
	S3AccessKey       string
	S3SecretAccessKey string
	S3EndpointURL     string
	S3Bucket          string
	BaseDir           string       // Base directory for storing etag file
	LeaseKey          string       // Optional custom lease key (defaults to "sprite.lock")
	Logger            *slog.Logger // Optional logger (defaults to no-op logger)
}

// LeaseInfo represents the lease data stored in S3
type LeaseInfo struct {
	MachineID  string    `json:"machine_id"`
	ExpiresAt  time.Time `json:"expires_at"`
	AcquiredAt time.Time `json:"acquired_at"`
}

// New creates a new Leaser instance
func New(config Config) *Leaser {
	// Use environment variables for Tigris configuration
	primaryRegion := os.Getenv("SPRITE_PRIMARY_REGION")
	if primaryRegion == "" {
		primaryRegion = "ord" // Default region
	}

	machineID := os.Getenv("FLY_MACHINE_ID")
	if machineID == "" {
		// Fallback to hostname if machine ID not set
		machineID, _ = os.Hostname()
	}

	leaseKey := config.LeaseKey
	if leaseKey == "" {
		leaseKey = "sprite.lock"
	}

	// Set up logger
	logger := config.Logger
	if logger == nil {
		// Create a no-op logger that discards all output
		logger = slog.New(slog.NewTextHandler(io.Discard, nil))
	}

	// Create AWS config
	awsCfg := aws.Config{
		Region: primaryRegion,
		Credentials: credentials.NewStaticCredentialsProvider(
			config.S3AccessKey,
			config.S3SecretAccessKey,
			"",
		),
	}

	// Create S3 client with custom endpoint
	s3Client := s3.NewFromConfig(awsCfg, func(o *s3.Options) {
		o.BaseEndpoint = aws.String(config.S3EndpointURL)
	})

	return &Leaser{
		s3Client:      s3Client,
		bucketName:    config.S3Bucket,
		primaryRegion: primaryRegion,
		machineID:     machineID,
		leaseKey:      leaseKey,
		baseDir:       config.BaseDir,
		etagFilePath:  filepath.Join(config.BaseDir, ".sprite-lease-etag"),
		stopCh:        make(chan struct{}),
		stoppedCh:     make(chan struct{}),
		logger:        logger,
	}
}

// NewWithS3Client creates a Leaser with a custom S3 client (for testing)
func NewWithS3Client(s3Client S3API, bucketName, leaseKey, machineID, baseDir string) *Leaser {
	return &Leaser{
		s3Client:      s3Client,
		bucketName:    bucketName,
		primaryRegion: "test-region",
		machineID:     machineID,
		leaseKey:      leaseKey,
		baseDir:       baseDir,
		etagFilePath:  filepath.Join(baseDir, ".sprite-lease-etag"),
		stopCh:        make(chan struct{}),
		stoppedCh:     make(chan struct{}),
		logger:        slog.New(slog.NewTextHandler(io.Discard, nil)),
	}
}

// Wait blocks until the lease is successfully acquired
func (l *Leaser) Wait(ctx context.Context) error {
	// 1. Attempt to acquire lease optimistically with etag stored on disk
	var initialETag string
	if data, err := os.ReadFile(l.etagFilePath); err == nil {
		initialETag = string(bytes.TrimSpace(data))
		l.logger.Debug("Read existing etag from file", "etag", initialETag)
	} else {
		l.logger.Debug("No existing etag file found, will attempt to create new lease")
	}

	acquired, etag, err := l.tryAcquireLease(ctx, initialETag)
	if err != nil {
		return fmt.Errorf("failed to try acquire lease: %w", err)
	}

	if acquired {
		// Success! No need to wait
		l.currentETag = etag
		l.logger.Info("Successfully acquired lease", "etag", etag)
		l.startLeaseRefresh()
		return nil
	}

	// Conditional check failed - our etag is stale, delete it
	if err := os.Remove(l.etagFilePath); err != nil && !os.IsNotExist(err) {
		l.logger.Debug("Failed to remove stale etag file", "error", err)
	} else {
		l.logger.Debug("Removed stale etag file")
	}

	// 2. If there's a conflict, read current lease info
	l.logger.Info("Lease acquisition failed, reading current lease info...")
	currentLease, currentETag, expired, err := l.checkCurrentLease(ctx)
	if err != nil {
		return fmt.Errorf("failed to check current lease: %w", err)
	}

	// 3. If expired, or held by the same machine, use current etag for acquisition
	if expired || (currentLease != nil && currentLease.MachineID == l.machineID) {
		l.logger.Info("Lease is expired or held by us, attempting acquisition with current etag", "machineID", l.machineID)

		// Use the ETag we already got from checkCurrentLease
		// If the lease didn't exist (currentLease == nil), currentETag will be empty string
		acquired, etag, err := l.tryAcquireLease(ctx, currentETag)
		if err != nil {
			return fmt.Errorf("failed to acquire lease with current etag: %w", err)
		}

		if acquired {
			l.currentETag = etag
			l.logger.Info("Successfully acquired lease with current etag", "etag", etag)
			l.startLeaseRefresh()
			return nil
		}
	}

	// 4. If not expired AND held by a different machine, wait for lease
	if currentLease != nil && !expired && currentLease.MachineID != l.machineID {
		l.logger.Info("Lease held by different machine, waiting for lease to expire...", "currentHolder", currentLease.MachineID)
		return l.waitForLease(ctx)
	}

	// Should not reach here, but if we do, return error
	return fmt.Errorf("unexpected state in lease acquisition")
}

// LeaseAttemptCount returns the number of attempts made to acquire the lease
func (l *Leaser) LeaseAttemptCount() int {
	return l.attemptCount
}

// Stop stops the lease manager and cleanup
func (l *Leaser) Stop() {
	select {
	case <-l.stopCh:
		// Already stopped
		return
	default:
		close(l.stopCh)
	}

	if l.refreshTicker != nil {
		l.refreshTicker.Stop()
	}

	// Signal that stop is complete - only close if not already closed
	select {
	case <-l.stoppedCh:
		// Already closed
	default:
		close(l.stoppedCh)
	}
}

// tryAcquireLease attempts to acquire the lease once
func (l *Leaser) tryAcquireLease(ctx context.Context, ifMatch string) (bool, string, error) {
	l.attemptCount++

	leaseInfo := LeaseInfo{
		MachineID:  l.machineID,
		ExpiresAt:  time.Now().Add(1 * time.Hour),
		AcquiredAt: time.Now(),
	}

	data, err := json.Marshal(leaseInfo)
	if err != nil {
		return false, "", fmt.Errorf("failed to marshal lease info: %w", err)
	}

	// Create the put object input
	input := &s3.PutObjectInput{
		Bucket:      aws.String(l.bucketName),
		Key:         aws.String(l.leaseKey),
		Body:        bytes.NewReader(data),
		ContentType: aws.String("application/json"),
	}

	// Set conditional headers based on the ifMatch parameter
	if ifMatch == "" {
		// We want to create the object only if it doesn't exist
		// Use IfNoneMatch with "*" to ensure it doesn't exist
		input.IfNoneMatch = aws.String("*")
	} else {
		// We have an existing ETag, use it for conditional update
		input.IfMatch = aws.String(ifMatch)
	}

	// Attempt to put the object with X-Tigris-Regions header
	output, err := l.s3Client.PutObject(ctx, input, func(o *s3.Options) {
		o.APIOptions = append(o.APIOptions, func(stack *middleware.Stack) error {
			return stack.Build.Add(middleware.BuildMiddlewareFunc("AddTigrisRegionsHeader", func(
				ctx context.Context, in middleware.BuildInput, next middleware.BuildHandler,
			) (
				out middleware.BuildOutput, metadata middleware.Metadata, err error,
			) {
				switch v := in.Request.(type) {
				case *smithyhttp.Request:
					v.Header.Set("X-Tigris-Regions", l.primaryRegion)
				}
				return next.HandleBuild(ctx, in)
			}), middleware.After)
		})
	})
	if err != nil {
		// Check for specific error conditions
		errStr := err.Error()
		if strings.Contains(errStr, "PreconditionFailed") ||
			strings.Contains(errStr, "412") ||
			strings.Contains(errStr, "ConditionalRequestConflict") ||
			strings.Contains(errStr, "409") {
			// Conditional check failed - someone else has the lease or it changed
			l.logger.Debug("Lease acquisition failed: conditional check failed")
			return false, "", nil
		}
		return false, "", fmt.Errorf("failed to put lease object: %w", err)
	}

	// Successfully acquired lease
	etag := ""
	if output.ETag != nil {
		etag = strings.Trim(*output.ETag, `"`)
	}

	// Write etag to file immediately upon successful acquisition
	if err := os.WriteFile(l.etagFilePath, []byte(etag), 0644); err != nil {
		l.logger.Warn("Failed to write etag file", "error", err)
		// Don't fail the lease acquisition for file write errors
	} else {
		l.logger.Debug("Successfully wrote etag to file", "path", l.etagFilePath)
	}

	l.logger.Info("Successfully acquired/updated lease", "etag", etag)
	return true, etag, nil
}

// checkCurrentLease reads the current lease and returns the lease info and whether it's expired
func (l *Leaser) checkCurrentLease(ctx context.Context) (*LeaseInfo, string, bool, error) {
	// Get the lease object
	getInput := &s3.GetObjectInput{
		Bucket: aws.String(l.bucketName),
		Key:    aws.String(l.leaseKey),
	}

	output, err := l.s3Client.GetObject(ctx, getInput)
	if err != nil {
		// If object doesn't exist, lease is available
		if strings.Contains(err.Error(), "NoSuchKey") || strings.Contains(err.Error(), "404") {
			return nil, "", true, nil
		}
		return nil, "", false, fmt.Errorf("failed to get lease object: %w", err)
	}
	defer output.Body.Close()

	// Extract ETag from response
	etag := ""
	if output.ETag != nil {
		etag = strings.Trim(*output.ETag, `"`)
	}

	// Read and parse the lease info
	data, err := io.ReadAll(output.Body)
	if err != nil {
		return nil, "", false, fmt.Errorf("failed to read lease body: %w", err)
	}

	var leaseInfo LeaseInfo
	if err := json.Unmarshal(data, &leaseInfo); err != nil {
		return nil, "", false, fmt.Errorf("failed to unmarshal lease info: %w", err)
	}

	// Check if lease is expired
	expired := time.Now().After(leaseInfo.ExpiresAt)
	if expired {
		l.logger.Info("Current lease has expired",
			"holder", leaseInfo.MachineID,
			"expiredAt", leaseInfo.ExpiresAt.Format(time.RFC3339))
	} else {
		l.logger.Info("Current lease is active",
			"holder", leaseInfo.MachineID,
			"expiresAt", leaseInfo.ExpiresAt.Format(time.RFC3339))
	}

	return &leaseInfo, etag, expired, nil
}

// getCurrentETag gets the current ETag of the lease object
func (l *Leaser) getCurrentETag(ctx context.Context) (string, error) {
	headInput := &s3.HeadObjectInput{
		Bucket: aws.String(l.bucketName),
		Key:    aws.String(l.leaseKey),
	}

	output, err := l.s3Client.HeadObject(ctx, headInput)
	if err != nil {
		return "", fmt.Errorf("failed to head lease object: %w", err)
	}

	if output.ETag == nil {
		return "", fmt.Errorf("no etag returned from head object")
	}

	return strings.Trim(*output.ETag, `"`), nil
}

// waitForLease waits for the lease to become available
func (l *Leaser) waitForLease(ctx context.Context) error {
	checkInterval := 5 * time.Second
	maxCheckInterval := 1 * time.Minute

	// Check immediately first, don't wait
	for {
		currentLease, currentETag, expired, err := l.checkCurrentLease(ctx)
		if err != nil {
			l.logger.Error("Error checking current lease", "error", err)
		} else {
			if currentLease == nil || expired {
				l.logger.Info("Lease is now available, attempting to acquire...")

				// Use the ETag we got from checkCurrentLease
				// If currentLease is nil (object doesn't exist), currentETag will be empty string
				acquired, etag, err := l.tryAcquireLease(ctx, currentETag)
				if err != nil {
					l.logger.Error("Error trying to acquire lease", "error", err)
				} else if acquired {
					l.currentETag = etag
					l.logger.Info("Successfully acquired lease after waiting", "etag", etag)
					l.startLeaseRefresh()
					return nil
				}
			} else {
				// Lease still held by someone else
				timeUntilExpiry := time.Until(currentLease.ExpiresAt)

				// Adjust check interval based on time until expiry
				if timeUntilExpiry <= 0 {
					// Already expired, check immediately on next iteration
					checkInterval = 1 * time.Millisecond
				} else if timeUntilExpiry < 30*time.Second {
					checkInterval = 5 * time.Second
				} else if timeUntilExpiry < 5*time.Minute {
					checkInterval = 15 * time.Second
				} else {
					checkInterval = checkInterval * 2
					if checkInterval > maxCheckInterval {
						checkInterval = maxCheckInterval
					}
				}

				l.logger.Info("Lease held by another machine, waiting",
					"holder", currentLease.MachineID,
					"expiresIn", timeUntilExpiry.Round(time.Second),
					"nextCheckIn", checkInterval)
			}
		}

		// Wait before next check
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-time.After(checkInterval):
			// Continue to next iteration
		}
	}
}

// startLeaseRefresh starts the background lease refresh goroutine
func (l *Leaser) startLeaseRefresh() {
	l.refreshTicker = time.NewTicker(30 * time.Minute) // Refresh every 30 minutes

	go func() {
		for {
			select {
			case <-l.refreshTicker.C:
				ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
				acquired, etag, err := l.tryAcquireLease(ctx, l.currentETag)
				cancel()

				if err != nil {
					l.logger.Error("Error refreshing lease", "error", err)
				} else if !acquired {
					l.logger.Warn("Failed to refresh lease, another instance may have taken over")
				} else {
					l.currentETag = etag
					l.logger.Debug("Successfully refreshed lease", "etag", etag)
				}
			case <-l.stopCh:
				return
			}
		}
	}()
}
