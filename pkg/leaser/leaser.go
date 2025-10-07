package leaser

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log/slog"
	"net"
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
	errCh         chan error
	currentETag   string
	logger        *slog.Logger

	// Fly.io specific fields
	isFlyEnvironment bool
	flyAppName       string
	flyPrivateIP     string
	leaseDuration    time.Duration
	refreshInterval  time.Duration

	// Refresh tracking
	currentRefreshCount int

	// Lifecycle state
	// Note: Start() and Stop() should not be called concurrently
	// Expected usage: Start() once, then Stop() once, then optionally Start() again
	started bool

	// Verifiers for external resources
	// These check actual system state, not internal Go values
	setupVerifiers   []func(context.Context) error // verify resources exist
	cleanupVerifiers []func(context.Context) error // verify resources cleaned up
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
	MachineID    string    `json:"machine_id"`
	ExpiresAt    time.Time `json:"expires_at"`
	AcquiredAt   time.Time `json:"acquired_at"`
	RefreshCount int       `json:"refresh_count"`
}

// ExternalResource represents an external resource managed by a component
type ExternalResource struct {
	Type            string       // "process", "mount", "file", "s3_object", "loop_device", "goroutine"
	Identifier      string       // PID, mount path, file path, S3 key, loop device name
	Description     string       // Human-readable description
	VerifyCleanedUp func() error // Function to verify this resource is cleaned up
}

// MapFlyRegionToTigris maps Fly.io region codes to Tigris region codes.
// Returns empty string if the region should not be mapped (e.g., "auto").
// Based on geographical proximity and available Tigris regions from:
// https://www.tigrisdata.com/docs/concepts/regions/
func MapFlyRegionToTigris(flyRegion string) string {
	// Handle special cases
	if flyRegion == "" || flyRegion == "auto" {
		return ""
	}

	// Direct mappings (regions that exist in both systems)
	directMappings := map[string]string{
		"ams": "ams", // Amsterdam
		"ord": "ord", // Chicago
		"dfw": "dfw", // Dallas
		"fra": "fra", // Frankfurt
		"iad": "iad", // Ashburn, Virginia
		"lhr": "lhr", // London
		"ewr": "ewr", // Newark
		"gru": "gru", // Sao Paulo
		"sin": "sin", // Singapore
		"sjc": "sjc", // San Jose
		"syd": "syd", // Sydney
		"nrt": "nrt", // Tokyo
		"jnb": "jnb", // Johannesburg
	}

	if tigrisRegion, ok := directMappings[flyRegion]; ok {
		return tigrisRegion
	}

	// Geographical mappings for Fly regions not in Tigris
	geoMappings := map[string]string{
		// US West
		"lax": "sjc", // Los Angeles -> San Jose
		"sea": "sjc", // Seattle -> San Jose
		"den": "sjc", // Denver -> San Jose
		"phx": "sjc", // Phoenix -> San Jose

		// US Central
		"yyz": "ord", // Toronto -> Chicago
		"yul": "ord", // Montreal -> Chicago
		"yyc": "ord", // Calgary -> Chicago

		// US East
		"bos": "ewr", // Boston -> Newark
		"atl": "iad", // Atlanta -> Ashburn
		"mia": "iad", // Miami -> Ashburn

		// Europe
		"cdg": "fra", // Paris -> Frankfurt
		"mad": "fra", // Madrid -> Frankfurt
		"arn": "fra", // Stockholm -> Frankfurt
		"waw": "fra", // Warsaw -> Frankfurt

		// Asia Pacific
		"hkg": "sin", // Hong Kong -> Singapore
		"tpe": "nrt", // Taipei -> Tokyo
		"bom": "sin", // Mumbai -> Singapore
		"maa": "sin", // Chennai -> Singapore

		// South America
		"eze": "gru", // Buenos Aires -> Sao Paulo
		"scl": "gru", // Santiago -> Sao Paulo
		"bog": "gru", // Bogota -> Sao Paulo

		// Oceania
		"mel": "syd", // Melbourne -> Sydney
		"akl": "syd", // Auckland -> Sydney

		// Middle East/Africa
		"dxb": "jnb", // Dubai -> Johannesburg (closest option)
		"tlv": "fra", // Tel Aviv -> Frankfurt
		"cpt": "jnb", // Cape Town -> Johannesburg
	}

	if tigrisRegion, ok := geoMappings[flyRegion]; ok {
		return tigrisRegion
	}

	// Unknown region - return empty to let Tigris use default routing
	return ""
}

// New creates a new Leaser instance
func New(config Config) *Leaser {
	// Use environment variables for Tigris configuration
	primaryRegion := os.Getenv("SPRITE_PRIMARY_REGION")
	if primaryRegion == "" {
		primaryRegion = "iad" // Default region
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

	// Detect Fly environment and set appropriate durations
	isFlyEnvironment := os.Getenv("FLY_MACHINE_ID") != ""
	flyAppName := os.Getenv("FLY_APP_NAME")
	flyPrivateIP := os.Getenv("FLY_PRIVATE_IP")

	// Use 15 minute lease, 5 minute refresh globally
	leaseDuration := 15 * time.Minute
	refreshInterval := 5 * time.Minute

	if isFlyEnvironment {
		logger.Info("Running in Fly environment",
			"machineID", machineID,
			"appName", flyAppName,
			"privateIP", flyPrivateIP)
	}

	logger.Debug("Lease configuration",
		"leaseDuration", leaseDuration,
		"refreshInterval", refreshInterval)

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

	// started is initialized to false by default (atomic.Bool zero value)
	return &Leaser{
		s3Client:            s3Client,
		bucketName:          config.S3Bucket,
		primaryRegion:       primaryRegion,
		machineID:           machineID,
		leaseKey:            leaseKey,
		baseDir:             config.BaseDir,
		etagFilePath:        filepath.Join(config.BaseDir, ".sprite-lease-etag"),
		stopCh:              make(chan struct{}),
		stoppedCh:           make(chan struct{}),
		errCh:               make(chan error, 1),
		logger:              logger,
		isFlyEnvironment:    isFlyEnvironment,
		flyAppName:          flyAppName,
		flyPrivateIP:        flyPrivateIP,
		leaseDuration:       leaseDuration,
		refreshInterval:     refreshInterval,
		currentRefreshCount: 0,
	}
}

// NewWithS3Client creates a Leaser with a custom S3 client (for testing)
func NewWithS3Client(s3Client S3API, bucketName, leaseKey, machineID, baseDir string) *Leaser {
	return &Leaser{
		s3Client:            s3Client,
		bucketName:          bucketName,
		primaryRegion:       "test-region",
		machineID:           machineID,
		leaseKey:            leaseKey,
		baseDir:             baseDir,
		etagFilePath:        filepath.Join(baseDir, ".sprite-lease-etag"),
		stopCh:              make(chan struct{}),
		stoppedCh:           make(chan struct{}),
		errCh:               make(chan error, 1),
		logger:              slog.New(slog.NewTextHandler(io.Discard, nil)),
		isFlyEnvironment:    false,
		flyAppName:          "",
		flyPrivateIP:        "",
		leaseDuration:       15 * time.Minute, // Updated to match global default
		refreshInterval:     5 * time.Minute,  // Updated to match global default
		currentRefreshCount: 0,
	}
}

// Start acquires the lease and starts the refresh goroutine
// Returns when lease is acquired and refresh is running
// Returns error if already started
func (l *Leaser) Start(ctx context.Context) error {
	if l.started {
		return fmt.Errorf("leaser already started")
	}
	l.started = true

	// Clear verifiers from any previous run
	l.setupVerifiers = nil
	l.cleanupVerifiers = nil

	// Recreate channels if they were closed by a previous Stop()
	// This enables restart after Stop()
	select {
	case <-l.stopCh:
		l.stopCh = make(chan struct{})
	default:
	}
	select {
	case <-l.stoppedCh:
		l.stoppedCh = make(chan struct{})
	default:
	}
	// errCh is buffered, so we can just drain and reuse it
	select {
	case <-l.errCh:
	default:
	}

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
		l.trackResources()
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
			l.trackResources()
			l.startLeaseRefresh()
			return nil
		}
	}

	// 4. If not expired AND held by a different machine, wait for lease
	if currentLease != nil && !expired && currentLease.MachineID != l.machineID {
		// In Fly environment, check if we're the only instance
		if l.isFlyEnvironment && l.isOnlyInstance() {
			// Check if lease was refreshed more than 5 minutes ago
			timeSinceAcquired := time.Since(currentLease.AcquiredAt)
			if timeSinceAcquired > 5*time.Minute {
				l.logger.Info("Detected as only instance with stale lease, attempting takeover",
					"currentHolder", currentLease.MachineID,
					"timeSinceAcquired", timeSinceAcquired)

				// Try to acquire the lease using the current ETag
				acquired, etag, err := l.tryAcquireLease(ctx, currentETag)
				if err != nil {
					l.logger.Error("Failed to takeover stale lease", "error", err)
				} else if acquired {
					l.currentETag = etag
					l.logger.Info("Successfully took over stale lease as only instance", "etag", etag)
					l.trackResources()
					l.startLeaseRefresh()
					return nil
				}
			} else {
				l.logger.Info("Only instance but lease is fresh, waiting",
					"timeSinceAcquired", timeSinceAcquired)
			}
		}

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

// RefreshCount returns the current refresh count of the lease
func (l *Leaser) RefreshCount() int {
	return l.currentRefreshCount
}

// Wait blocks until Stop() completes or a panic occurs
// Can be called multiple times safely
func (l *Leaser) Wait() error {
	select {
	case <-l.stoppedCh:
		return nil
	case err := <-l.errCh:
		return err
	}
}

// Stop initiates shutdown then waits for completion
// Can be called multiple times safely
// May return error but MUST forcefully clean up even on error
func (l *Leaser) Stop(ctx context.Context) error {
	// Signal shutdown
	select {
	case <-l.stopCh:
		// Already stopping
	default:
		close(l.stopCh)
	}

	// Do cleanup work - stop the ticker if it exists
	// The refresh goroutine will exit when it sees stopCh closed
	if l.refreshTicker != nil {
		l.refreshTicker.Stop()
		l.refreshTicker = nil
	}

	// Give the refresh goroutine a moment to exit
	// In production this is fine since we're stopping anyway
	time.Sleep(10 * time.Millisecond)

	// Signal that stop is complete
	select {
	case <-l.stoppedCh:
		// Already closed
	default:
		close(l.stoppedCh)
	}

	// Mark as not started so it can be restarted
	l.started = false

	return nil
}

// isOnlyInstance checks if this is the only instance in Fly environment
func (l *Leaser) isOnlyInstance() bool {
	if !l.isFlyEnvironment || l.flyAppName == "" || l.flyPrivateIP == "" {
		return false
	}

	// Lookup AAAA records for the app's internal hostname
	hostname := fmt.Sprintf("%s.internal", l.flyAppName)
	ips, err := net.LookupIP(hostname)
	if err != nil {
		l.logger.Debug("Failed to lookup DNS records", "hostname", hostname, "error", err)
		return false
	}

	// Filter for IPv6 addresses (AAAA records)
	var ipv6Addrs []string
	for _, ip := range ips {
		if ip.To4() == nil && ip.To16() != nil {
			// This is an IPv6 address
			ipv6Addrs = append(ipv6Addrs, ip.String())
		}
	}

	l.logger.Debug("DNS lookup results", "hostname", hostname, "ipv6Addrs", ipv6Addrs, "ourIP", l.flyPrivateIP)

	// Check if there's only one IPv6 address and it matches our private IP
	if len(ipv6Addrs) == 1 && ipv6Addrs[0] == l.flyPrivateIP {
		l.logger.Info("Detected as only instance", "ip", l.flyPrivateIP)
		return true
	}

	return false
}

// tryAcquireLease attempts to acquire the lease once
func (l *Leaser) tryAcquireLease(ctx context.Context, ifMatch string) (bool, string, error) {
	l.attemptCount++

	// If we have an ifMatch (doing a refresh), increment the refresh count
	refreshCount := l.currentRefreshCount
	if ifMatch != "" && ifMatch == l.currentETag {
		// This is a refresh of our own lease
		refreshCount++
	} else if ifMatch == "" {
		// This is a new lease acquisition
		refreshCount = 0
	}
	// If ifMatch is set but doesn't match our currentETag, we're taking over someone else's lease
	// In that case, keep the existing currentRefreshCount which should have been set from checkCurrentLease

	leaseInfo := LeaseInfo{
		MachineID:    l.machineID,
		ExpiresAt:    time.Now().Add(l.leaseDuration),
		AcquiredAt:   time.Now(),
		RefreshCount: refreshCount,
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
					// Map Fly region to valid Tigris region
					tigrisRegion := MapFlyRegionToTigris(l.primaryRegion)
					if tigrisRegion != "" {
						v.Header.Set("X-Tigris-Regions", tigrisRegion)
					}
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

	// Update our current refresh count
	l.currentRefreshCount = refreshCount

	l.logger.Info("Successfully acquired/updated lease", "etag", etag, "refreshCount", refreshCount)
	return true, etag, nil
}

// checkCurrentLease reads the current lease and returns the lease info and whether it's expired
func (l *Leaser) checkCurrentLease(ctx context.Context) (*LeaseInfo, string, bool, error) {
	// Get the lease object
	getInput := &s3.GetObjectInput{
		Bucket: aws.String(l.bucketName),
		Key:    aws.String(l.leaseKey),
	}

	l.logger.Debug("Checking current lease", "bucket", l.bucketName, "key", l.leaseKey)

	output, err := l.s3Client.GetObject(ctx, getInput)
	if err != nil {
		// Log the actual error for debugging
		l.logger.Debug("Error getting lease object", "error", err, "errorType", fmt.Sprintf("%T", err))

		// If object doesn't exist, lease is available
		errStr := err.Error()
		if strings.Contains(errStr, "NoSuchKey") ||
			strings.Contains(errStr, "404") ||
			strings.Contains(errStr, "NotFound") ||
			strings.Contains(errStr, "not found") ||
			strings.Contains(errStr, "does not exist") {
			l.logger.Info("Lease object does not exist, lease is available")
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

	// Save the refresh count from the existing lease
	l.currentRefreshCount = leaseInfo.RefreshCount

	// Check if lease is expired
	expired := time.Now().After(leaseInfo.ExpiresAt)
	if expired {
		l.logger.Info("Current lease has expired",
			"holder", leaseInfo.MachineID,
			"expiredAt", leaseInfo.ExpiresAt.Format(time.RFC3339),
			"refreshCount", leaseInfo.RefreshCount)
	} else {
		l.logger.Info("Current lease is active",
			"holder", leaseInfo.MachineID,
			"expiresAt", leaseInfo.ExpiresAt.Format(time.RFC3339),
			"refreshCount", leaseInfo.RefreshCount)
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

// verifyLeaseExists checks if the lease object actually exists
func (l *Leaser) verifyLeaseExists(ctx context.Context) bool {
	headInput := &s3.HeadObjectInput{
		Bucket: aws.String(l.bucketName),
		Key:    aws.String(l.leaseKey),
	}

	_, err := l.s3Client.HeadObject(ctx, headInput)
	if err != nil {
		errStr := err.Error()
		if strings.Contains(errStr, "NoSuchKey") ||
			strings.Contains(errStr, "404") ||
			strings.Contains(errStr, "NotFound") ||
			strings.Contains(errStr, "not found") ||
			strings.Contains(errStr, "does not exist") {
			l.logger.Debug("HeadObject confirms lease does not exist")
			return false
		}
		l.logger.Debug("HeadObject error (assuming exists)", "error", err)
		return true // Assume it exists if we get other errors
	}
	l.logger.Debug("HeadObject confirms lease exists")
	return true
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
					l.trackResources()
					l.startLeaseRefresh()
					return nil
				}
			} else {
				// Lease still held by someone else
				timeUntilExpiry := time.Until(currentLease.ExpiresAt)

				// Double-check if the lease really exists (handle eventual consistency)
				if !l.verifyLeaseExists(ctx) {
					l.logger.Info("Lease appeared active but verification shows it doesn't exist, retrying immediately")
					// Force immediate retry
					checkInterval = 1 * time.Millisecond
				} else {
					// In Fly environment, check if we've become the only instance
					if l.isFlyEnvironment && currentLease.MachineID != l.machineID {
						if l.isOnlyInstance() {
							timeSinceAcquired := time.Since(currentLease.AcquiredAt)
							if timeSinceAcquired > 5*time.Minute {
								l.logger.Info("Became only instance with stale lease during wait, attempting takeover",
									"currentHolder", currentLease.MachineID,
									"timeSinceAcquired", timeSinceAcquired)

								acquired, etag, err := l.tryAcquireLease(ctx, currentETag)
								if err != nil {
									l.logger.Error("Failed to takeover stale lease", "error", err)
								} else if acquired {
									l.currentETag = etag
									l.logger.Info("Successfully took over stale lease as only instance", "etag", etag)
									l.trackResources()
									l.startLeaseRefresh()
									return nil
								}
							}
						}
					}

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

// trackResources adds verifiers for acquired resources
func (l *Leaser) trackResources() {
	// Setup verifier: check etag file exists and has content
	l.setupVerifiers = append(l.setupVerifiers, func(ctx context.Context) error {
		if _, err := os.Stat(l.etagFilePath); os.IsNotExist(err) {
			return fmt.Errorf("etag file does not exist: %s", l.etagFilePath)
		}
		data, err := os.ReadFile(l.etagFilePath)
		if err != nil {
			return fmt.Errorf("failed to read etag file: %w", err)
		}
		if len(bytes.TrimSpace(data)) == 0 {
			return fmt.Errorf("etag file is empty")
		}
		return nil
	})

	// Cleanup verifier: check ticker is nil (goroutine stopped)
	l.cleanupVerifiers = append(l.cleanupVerifiers, func(ctx context.Context) error {
		if l.refreshTicker != nil {
			return fmt.Errorf("refresh ticker still exists")
		}
		return nil
	})
}

// startLeaseRefresh starts the background lease refresh goroutine
func (l *Leaser) startLeaseRefresh() {
	l.refreshTicker = time.NewTicker(l.refreshInterval)
	ticker := l.refreshTicker // Capture ticker locally so goroutine doesn't race on l.refreshTicker

	go func() {
		for {
			select {
			case <-ticker.C:
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

// SetupVerifiers returns functions that verify resources are set up correctly
// Each function checks actual system state (files, processes, etc.)
func (l *Leaser) SetupVerifiers() []func(context.Context) error {
	return l.setupVerifiers
}

// CleanupVerifiers returns functions that verify resources are cleaned up
// Each function checks actual system state (files, processes, etc.)
func (l *Leaser) CleanupVerifiers() []func(context.Context) error {
	return l.cleanupVerifiers
}
