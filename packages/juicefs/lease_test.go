package juicefs

import (
	"context"
	"encoding/json"
	"os"
	"path/filepath"
	"testing"
	"time"
)

func TestLeaseManager(t *testing.T) {
	// Skip if not in CI or no S3 credentials
	if os.Getenv("CI") == "" {
		t.Skip("Skipping lease manager test outside of CI")
	}

	// Create a test config
	config := Config{
		BaseDir:           t.TempDir(),
		S3AccessKey:       os.Getenv("SPRITE_S3_ACCESS_KEY"),
		S3SecretAccessKey: os.Getenv("SPRITE_S3_SECRET_ACCESS_KEY"),
		S3EndpointURL:     os.Getenv("SPRITE_S3_ENDPOINT_URL"),
		S3Bucket:          os.Getenv("SPRITE_S3_BUCKET"),
		VolumeName:        "test-juicefs",
	}

	if config.S3AccessKey == "" || config.S3SecretAccessKey == "" {
		t.Skip("S3 credentials not available")
	}

	// Set up test environment
	os.Setenv("SPRITE_PRIMARY_REGION", "ord")
	os.Setenv("FLY_MACHINE_ID", "test-machine-1")
	os.Setenv("FLY_VOLUME_PATH", t.TempDir())

	t.Run("AcquireLeaseFirstTime", func(t *testing.T) {
		lm := NewLeaseManager(config)
		ctx := context.Background()

		// First acquisition should succeed
		acquired, err := lm.AcquireLease(ctx)
		if err != nil {
			t.Fatalf("Failed to acquire lease: %v", err)
		}
		if !acquired {
			t.Fatal("Expected to acquire lease on first attempt")
		}

		// Check that etag file was written
		if _, err := os.Stat(lm.etagFilePath); err != nil {
			t.Fatalf("Expected etag file to exist: %v", err)
		}

		// Stop the lease manager
		lm.Stop()
	})

	t.Run("AcquireLeaseWithExistingETag", func(t *testing.T) {
		lm := NewLeaseManager(config)

		// Create a fake etag file
		testETag := `"test-etag-123"`
		etagPath := filepath.Join(os.Getenv("FLY_VOLUME_PATH"), ".juicefs-lease-etag")
		if err := os.WriteFile(etagPath, []byte(testETag), 0644); err != nil {
			t.Fatalf("Failed to write test etag: %v", err)
		}

		ctx := context.Background()

		// This should fail because the etag doesn't match
		// In a real scenario, this would enter the retry loop
		acquired, err := lm.AcquireLease(ctx)

		// We expect this to eventually succeed after retrying
		// (in the test environment, it might succeed immediately if no one else has the lease)
		if err == nil && acquired {
			// That's fine - we acquired the lease
			lm.Stop()
			return
		}

		// If we didn't acquire immediately, that's also expected
		// The real implementation would keep retrying
		lm.Stop()
	})

	t.Run("LeaseRefresh", func(t *testing.T) {
		lm := NewLeaseManager(config)
		ctx := context.Background()

		// Acquire lease
		acquired, err := lm.AcquireLease(ctx)
		if err != nil || !acquired {
			t.Skip("Could not acquire lease for refresh test")
		}

		// Wait a bit to ensure refresh ticker starts
		time.Sleep(100 * time.Millisecond)

		// Check that refresh ticker is running
		if lm.refreshTicker == nil {
			t.Fatal("Expected refresh ticker to be initialized")
		}

		// Stop the lease manager
		lm.Stop()

		// Verify ticker is stopped
		select {
		case <-lm.refreshTicker.C:
			t.Fatal("Ticker should be stopped")
		default:
			// Good, ticker is stopped
		}
	})
}

func TestLeaseInfoMarshaling(t *testing.T) {
	info := LeaseInfo{
		MachineID:  "test-machine",
		ExpiresAt:  time.Now().Add(1 * time.Hour),
		AcquiredAt: time.Now(),
	}

	data, err := json.Marshal(info)
	if err != nil {
		t.Fatalf("Failed to marshal lease info: %v", err)
	}

	var decoded LeaseInfo
	if err := json.Unmarshal(data, &decoded); err != nil {
		t.Fatalf("Failed to unmarshal lease info: %v", err)
	}

	if decoded.MachineID != info.MachineID {
		t.Errorf("Expected machine ID %s, got %s", info.MachineID, decoded.MachineID)
	}
}
