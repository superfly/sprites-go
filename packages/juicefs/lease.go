package juicefs

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
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

// S3API interface for S3 operations used by LeaseManager
type S3API interface {
	PutObject(ctx context.Context, params *s3.PutObjectInput, optFns ...func(*s3.Options)) (*s3.PutObjectOutput, error)
	GetObject(ctx context.Context, params *s3.GetObjectInput, optFns ...func(*s3.Options)) (*s3.GetObjectOutput, error)
	HeadObject(ctx context.Context, params *s3.HeadObjectInput, optFns ...func(*s3.Options)) (*s3.HeadObjectOutput, error)
}

// LeaseManager handles the Tigris lease for JuiceFS database safety
type LeaseManager struct {
	s3Client      S3API
	bucketName    string
	primaryRegion string
	machineID     string
	leaseKey      string
	etagFilePath  string
	refreshTicker *time.Ticker
	stopCh        chan struct{}
	currentETag   string
}

// LeaseInfo represents the lease data stored in Tigris
type LeaseInfo struct {
	MachineID  string    `json:"machine_id"`
	ExpiresAt  time.Time `json:"expires_at"`
	AcquiredAt time.Time `json:"acquired_at"`
}

// NewLeaseManager creates a new lease manager
func NewLeaseManager(config Config) *LeaseManager {
	return NewLeaseManagerWithKey(config, "")
}

// NewLeaseManagerWithKey creates a new lease manager with a custom lease key
func NewLeaseManagerWithKey(config Config, customKey string) *LeaseManager {
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

	// The etag file is stored in the base directory root path (not inside JuiceFS)
	baseDir := config.BaseDir
	if baseDir == "" {
		// Fallback to FLY_VOLUME_PATH for backward compatibility
		baseDir = os.Getenv("FLY_VOLUME_PATH")
		if baseDir == "" {
			baseDir = "/fly_vol" // Default path
		}
	}

	leaseKey := customKey
	if leaseKey == "" {
		leaseKey = "sprite.lock"
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

	return &LeaseManager{
		s3Client:      s3Client,
		bucketName:    config.S3Bucket,
		primaryRegion: primaryRegion,
		machineID:     machineID,
		leaseKey:      leaseKey,
		etagFilePath:  filepath.Join(baseDir, ".juicefs-lease-etag"),
		stopCh:        make(chan struct{}),
	}
}

// NewLeaseManagerWithS3Client creates a lease manager with a custom S3 client (for testing)
func NewLeaseManagerWithS3Client(s3Client S3API, bucketName, leaseKey, machineID, etagFilePath string) *LeaseManager {
	return &LeaseManager{
		s3Client:      s3Client,
		bucketName:    bucketName,
		primaryRegion: "test-region",
		machineID:     machineID,
		leaseKey:      leaseKey,
		etagFilePath:  etagFilePath,
		stopCh:        make(chan struct{}),
	}
}

// AcquireLease attempts to acquire the lease for JuiceFS
// Returns true if lease was acquired, false if it needs to restore from litestream
func (lm *LeaseManager) AcquireLease(ctx context.Context) (bool, error) {
	// 1. Attempt to acquire lease optimistically with etag (or "") stored on disk
	// tryAcquireLease will read the etag file if ifMatch is empty
	acquired, etag, err := lm.tryAcquireLease(ctx, "")
	if err != nil {
		return false, fmt.Errorf("failed to try acquire lease: %w", err)
	}

	if acquired {
		// Success! No litestream restore needed
		// etag file is already written by tryAcquireLease
		lm.currentETag = etag
		fmt.Printf("Successfully acquired lease with etag: %s\n", etag)
		lm.startLeaseRefresh()
		return true, nil
	}

	// 2. If there's a conflict, read current lease info
	fmt.Println("Lease acquisition failed, reading current lease info...")
	currentLease, expired, err := lm.checkCurrentLease(ctx)
	if err != nil {
		return false, fmt.Errorf("failed to check current lease: %w", err)
	}

	// 3. If expired, or the id is the same as our machine id, use current etag value for acquisition
	if expired || (currentLease != nil && currentLease.MachineID == lm.machineID) {
		fmt.Printf("Lease is expired or held by us (%s), attempting acquisition with current etag\n", lm.machineID)

		// Get current etag for the object
		currentETag, err := lm.getCurrentETag(ctx)
		if err != nil {
			return false, fmt.Errorf("failed to get current etag: %w", err)
		}

		acquired, etag, err := lm.tryAcquireLease(ctx, currentETag)
		if err != nil {
			return false, fmt.Errorf("failed to acquire lease with current etag: %w", err)
		}

		if acquired {
			// etag file is already written by tryAcquireLease
			lm.currentETag = etag
			fmt.Printf("Successfully acquired lease with current etag: %s\n", etag)
			lm.startLeaseRefresh()
			return true, nil
		}
	}

	// 4. If not expired AND machine id is different than ours, wait for lease
	if currentLease != nil && !expired && currentLease.MachineID != lm.machineID {
		fmt.Printf("Lease held by different machine (%s), waiting for lease to expire...\n", currentLease.MachineID)
		return false, lm.waitForLease(ctx)
	}

	// Should not reach here, but if we do, return error
	return false, fmt.Errorf("unexpected state in lease acquisition")
}

// tryAcquireLease attempts to acquire the lease once
func (lm *LeaseManager) tryAcquireLease(ctx context.Context, ifMatch string) (bool, string, error) {
	// If ifMatch is empty, try to read etag from file
	actualIfMatch := ifMatch
	if actualIfMatch == "" {
		if data, err := os.ReadFile(lm.etagFilePath); err == nil {
			actualIfMatch = string(bytes.TrimSpace(data))
			fmt.Printf("Read existing etag from file: %s\n", actualIfMatch)
		} else {
			// File doesn't exist, use empty string (will use IfNoneMatch)
			actualIfMatch = ""
			fmt.Printf("No existing etag file found, using empty etag\n")
		}
	}

	leaseInfo := LeaseInfo{
		MachineID:  lm.machineID,
		ExpiresAt:  time.Now().Add(1 * time.Hour),
		AcquiredAt: time.Now(),
	}

	data, err := json.Marshal(leaseInfo)
	if err != nil {
		return false, "", fmt.Errorf("failed to marshal lease info: %w", err)
	}

	// Create the put object input
	input := &s3.PutObjectInput{
		Bucket:      aws.String(lm.bucketName),
		Key:         aws.String(lm.leaseKey),
		Body:        bytes.NewReader(data),
		ContentType: aws.String("application/json"),
	}

	// Set conditional headers based on the actualIfMatch parameter
	if actualIfMatch == "" {
		// We want to create the object only if it doesn't exist
		// Use IfNoneMatch with "*" to ensure it doesn't exist
		input.IfNoneMatch = aws.String("*")
	} else {
		// We have an existing ETag, use it for conditional update
		input.IfMatch = aws.String(actualIfMatch)
	}

	// Attempt to put the object with X-Tigris-Regions header
	output, err := lm.s3Client.PutObject(ctx, input, func(o *s3.Options) {
		o.APIOptions = append(o.APIOptions, func(stack *middleware.Stack) error {
			return stack.Build.Add(middleware.BuildMiddlewareFunc("AddTigrisRegionsHeader", func(
				ctx context.Context, in middleware.BuildInput, next middleware.BuildHandler,
			) (
				out middleware.BuildOutput, metadata middleware.Metadata, err error,
			) {
				switch v := in.Request.(type) {
				case *smithyhttp.Request:
					v.Header.Set("X-Tigris-Regions", lm.primaryRegion)
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
			fmt.Printf("Lease acquisition failed: conditional check failed\n")
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
	if err := os.WriteFile(lm.etagFilePath, []byte(etag), 0644); err != nil {
		fmt.Printf("Warning: failed to write etag file: %v\n", err)
		// Don't fail the lease acquisition for file write errors
	} else {
		fmt.Printf("Successfully wrote etag to file: %s\n", lm.etagFilePath)
	}

	fmt.Printf("Successfully acquired/updated lease with new ETag: %s\n", etag)
	return true, etag, nil
}

// checkCurrentLease reads the current lease and returns the lease info and whether it's expired
func (lm *LeaseManager) checkCurrentLease(ctx context.Context) (*LeaseInfo, bool, error) {
	// Get the lease object
	getInput := &s3.GetObjectInput{
		Bucket: aws.String(lm.bucketName),
		Key:    aws.String(lm.leaseKey),
	}

	output, err := lm.s3Client.GetObject(ctx, getInput)
	if err != nil {
		// If object doesn't exist, lease is available
		if strings.Contains(err.Error(), "NoSuchKey") || strings.Contains(err.Error(), "404") {
			return nil, true, nil
		}
		return nil, false, fmt.Errorf("failed to get lease object: %w", err)
	}
	defer output.Body.Close()

	// Read and parse the lease info
	data, err := io.ReadAll(output.Body)
	if err != nil {
		return nil, false, fmt.Errorf("failed to read lease body: %w", err)
	}

	var leaseInfo LeaseInfo
	if err := json.Unmarshal(data, &leaseInfo); err != nil {
		return nil, false, fmt.Errorf("failed to unmarshal lease info: %w", err)
	}

	// Check if lease is expired
	expired := time.Now().After(leaseInfo.ExpiresAt)
	if expired {
		fmt.Printf("Current lease held by %s has expired (expired at %s)\n",
			leaseInfo.MachineID, leaseInfo.ExpiresAt.Format(time.RFC3339))
	} else {
		fmt.Printf("Current lease held by %s, expires at %s\n",
			leaseInfo.MachineID, leaseInfo.ExpiresAt.Format(time.RFC3339))
	}

	return &leaseInfo, expired, nil
}

// getCurrentETag gets the current ETag of the lease object
func (lm *LeaseManager) getCurrentETag(ctx context.Context) (string, error) {
	headInput := &s3.HeadObjectInput{
		Bucket: aws.String(lm.bucketName),
		Key:    aws.String(lm.leaseKey),
	}

	output, err := lm.s3Client.HeadObject(ctx, headInput)
	if err != nil {
		return "", fmt.Errorf("failed to head lease object: %w", err)
	}

	if output.ETag == nil {
		return "", fmt.Errorf("no etag returned from head object")
	}

	return strings.Trim(*output.ETag, `"`), nil
}

// waitForLease waits for the lease to become available
func (lm *LeaseManager) waitForLease(ctx context.Context) error {
	checkInterval := 5 * time.Second
	maxCheckInterval := 1 * time.Minute

	for {
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-time.After(checkInterval):
			currentLease, expired, err := lm.checkCurrentLease(ctx)
			if err != nil {
				fmt.Printf("Error checking current lease: %v\n", err)
				continue
			}

			if currentLease == nil || expired {
				fmt.Println("Lease is now available, attempting to acquire...")

				// Try to acquire with empty etag since lease expired or doesn't exist
				acquired, etag, err := lm.tryAcquireLease(ctx, "")
				if err != nil {
					fmt.Printf("Error trying to acquire lease: %v\n", err)
				} else if acquired {
					// etag file is already written by tryAcquireLease
					lm.currentETag = etag
					fmt.Printf("Successfully acquired lease after waiting with etag: %s\n", etag)
					lm.startLeaseRefresh()
					return nil
				}
			} else {
				// Lease still held by someone else
				timeUntilExpiry := time.Until(currentLease.ExpiresAt)

				// Adjust check interval based on time until expiry
				if timeUntilExpiry < 30*time.Second {
					checkInterval = 5 * time.Second
				} else if timeUntilExpiry < 5*time.Minute {
					checkInterval = 15 * time.Second
				} else {
					checkInterval = checkInterval * 2
					if checkInterval > maxCheckInterval {
						checkInterval = maxCheckInterval
					}
				}

				fmt.Printf("Lease held by %s, expires in %v. Checking again in %v\n",
					currentLease.MachineID, timeUntilExpiry.Round(time.Second), checkInterval)
			}
		}
	}
}

// startLeaseRefresh starts the background lease refresh goroutine
func (lm *LeaseManager) startLeaseRefresh() {
	lm.refreshTicker = time.NewTicker(30 * time.Minute) // Refresh every 30 minutes

	go func() {
		for {
			select {
			case <-lm.refreshTicker.C:
				ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
				acquired, etag, err := lm.tryAcquireLease(ctx, lm.currentETag)
				cancel()

				if err != nil {
					fmt.Printf("Error refreshing lease: %v\n", err)
				} else if !acquired {
					fmt.Println("WARNING: Failed to refresh lease, another instance may have taken over")
				} else {
					lm.currentETag = etag
					// etag file is already updated by tryAcquireLease
					fmt.Printf("Successfully refreshed lease with etag: %s\n", etag)
				}
			case <-lm.stopCh:
				return
			}
		}
	}()
}

// Stop stops the lease refresh
func (lm *LeaseManager) Stop() {
	if lm.refreshTicker != nil {
		lm.refreshTicker.Stop()
	}
	close(lm.stopCh)
}
