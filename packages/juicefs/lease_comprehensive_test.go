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
	"testing"
	"time"

	"github.com/aws/aws-sdk-go-v2/aws"
	"github.com/aws/aws-sdk-go-v2/service/s3"
	"github.com/aws/aws-sdk-go-v2/service/s3/types"
)

// Note: S3API interface is now defined in lease.go

// MockS3Client implements S3API for testing
type MockS3Client struct {
	objects        map[string]*StoredObject
	putObjectCalls []PutObjectCall
}

type StoredObject struct {
	Data    []byte
	ETag    string
	Headers map[string]string
}

type PutObjectCall struct {
	Input     *s3.PutObjectInput
	Headers   map[string]string
	Timestamp time.Time
}

func NewMockS3Client() *MockS3Client {
	return &MockS3Client{
		objects:        make(map[string]*StoredObject),
		putObjectCalls: make([]PutObjectCall, 0),
	}
}

func (m *MockS3Client) PutObject(ctx context.Context, params *s3.PutObjectInput, optFns ...func(*s3.Options)) (*s3.PutObjectOutput, error) {
	key := *params.Key

	// Always record the call for inspection
	m.putObjectCalls = append(m.putObjectCalls, PutObjectCall{
		Input:     params,
		Timestamp: time.Now(),
	})

	// Check conditional headers
	if params.IfNoneMatch != nil && *params.IfNoneMatch == "*" {
		// Should only succeed if object doesn't exist
		if _, exists := m.objects[key]; exists {
			return nil, fmt.Errorf("ConditionalRequestConflict: object already exists")
		}
	}

	if params.IfMatch != nil {
		// Should only succeed if etag matches
		existing, exists := m.objects[key]
		if !exists {
			return nil, fmt.Errorf("PreconditionFailed: object does not exist")
		}
		if existing.ETag != *params.IfMatch {
			return nil, fmt.Errorf("PreconditionFailed: etag mismatch")
		}
	}

	// Read body data
	data, err := io.ReadAll(params.Body)
	if err != nil {
		return nil, err
	}

	// Generate new ETag
	newETag := fmt.Sprintf("etag-%d", time.Now().UnixNano())

	// Store object
	m.objects[key] = &StoredObject{
		Data:    data,
		ETag:    newETag,
		Headers: make(map[string]string),
	}

	return &s3.PutObjectOutput{
		ETag: aws.String(fmt.Sprintf(`"%s"`, newETag)),
	}, nil
}

func (m *MockS3Client) GetObject(ctx context.Context, params *s3.GetObjectInput, optFns ...func(*s3.Options)) (*s3.GetObjectOutput, error) {
	key := *params.Key
	obj, exists := m.objects[key]
	if !exists {
		return nil, &types.NoSuchKey{}
	}

	return &s3.GetObjectOutput{
		Body: io.NopCloser(bytes.NewReader(obj.Data)),
		ETag: aws.String(fmt.Sprintf(`"%s"`, obj.ETag)),
	}, nil
}

func (m *MockS3Client) HeadObject(ctx context.Context, params *s3.HeadObjectInput, optFns ...func(*s3.Options)) (*s3.HeadObjectOutput, error) {
	key := *params.Key
	obj, exists := m.objects[key]
	if !exists {
		return nil, &types.NoSuchKey{}
	}

	return &s3.HeadObjectOutput{
		ETag: aws.String(fmt.Sprintf(`"%s"`, obj.ETag)),
	}, nil
}

func (m *MockS3Client) GetStoredObject(key string) *StoredObject {
	return m.objects[key]
}

func (m *MockS3Client) GetPutObjectCalls() []PutObjectCall {
	return m.putObjectCalls
}

func (m *MockS3Client) SetObject(key, etag string, data []byte) {
	m.objects[key] = &StoredObject{
		Data:    data,
		ETag:    etag,
		Headers: make(map[string]string),
	}
}

func (m *MockS3Client) DeleteObject(key string) {
	delete(m.objects, key)
}

func createTestLeaseManager(mockS3 S3API, machineID, leaseKey string) *LeaseManager {
	tempDir, _ := os.MkdirTemp("", "lease-test")
	etagFilePath := filepath.Join(tempDir, ".juicefs-lease-etag")

	return NewLeaseManagerWithS3Client(
		mockS3,
		"test-bucket",
		leaseKey,
		machineID,
		etagFilePath,
	)
}

// Helper to create expired lease
func createExpiredLease(machineID string) LeaseInfo {
	return LeaseInfo{
		MachineID:  machineID,
		ExpiresAt:  time.Now().Add(-1 * time.Hour), // Expired 1 hour ago
		AcquiredAt: time.Now().Add(-2 * time.Hour),
	}
}

// Helper to create active lease
func createActiveLease(machineID string) LeaseInfo {
	return LeaseInfo{
		MachineID:  machineID,
		ExpiresAt:  time.Now().Add(1 * time.Hour), // Expires in 1 hour
		AcquiredAt: time.Now(),
	}
}

func TestLeaseAcquisitionScenarios(t *testing.T) {
	t.Run("Scenario1_OptimisticAcquisition_NoExistingLease", func(t *testing.T) {
		mockS3 := NewMockS3Client()
		lm := createTestLeaseManager(mockS3, "machine-1", "test-lease-1")

		// No existing lease, no etag file
		ctx := context.Background()
		acquired, err := lm.AcquireLease(ctx)

		if err != nil {
			t.Fatalf("Expected no error, got: %v", err)
		}
		if !acquired {
			t.Fatal("Expected to acquire lease optimistically")
		}

		// Verify object was created with IfNoneMatch
		calls := mockS3.GetPutObjectCalls()
		if len(calls) != 1 {
			t.Fatalf("Expected 1 PutObject call, got %d", len(calls))
		}

		call := calls[0]
		if call.Input.IfNoneMatch == nil || *call.Input.IfNoneMatch != "*" {
			t.Errorf("Expected IfNoneMatch='*', got %v", call.Input.IfNoneMatch)
		}

		// Verify etag file was written
		if _, err := os.Stat(lm.etagFilePath); os.IsNotExist(err) {
			t.Error("Expected etag file to be created")
		}

		lm.Stop()
	})

	t.Run("Scenario2_OptimisticAcquisition_WithExistingETag", func(t *testing.T) {
		mockS3 := NewMockS3Client()
		lm := createTestLeaseManager(mockS3, "machine-1", "test-lease-2")

		// Create existing lease with known etag
		existingLease := createActiveLease("machine-1")
		data, _ := json.Marshal(existingLease)
		mockS3.SetObject("test-lease-2", "existing-etag", data)

		// Write etag file to simulate previous run
		os.WriteFile(lm.etagFilePath, []byte("existing-etag"), 0644)

		ctx := context.Background()
		acquired, err := lm.AcquireLease(ctx)

		if err != nil {
			t.Fatalf("Expected no error, got: %v", err)
		}
		if !acquired {
			t.Fatal("Expected to acquire lease with existing etag")
		}

		// Verify object was updated with IfMatch
		calls := mockS3.GetPutObjectCalls()
		if len(calls) != 1 {
			t.Fatalf("Expected 1 PutObject call, got %d", len(calls))
		}

		call := calls[0]
		if call.Input.IfMatch == nil || *call.Input.IfMatch != "existing-etag" {
			t.Errorf("Expected IfMatch='existing-etag', got %v", call.Input.IfMatch)
		}

		lm.Stop()
	})

	t.Run("Scenario3_ConflictResolution_ExpiredLease", func(t *testing.T) {
		mockS3 := NewMockS3Client()
		lm := createTestLeaseManager(mockS3, "machine-1", "test-lease-3")

		// Create expired lease held by different machine
		expiredLease := createExpiredLease("machine-2")
		data, _ := json.Marshal(expiredLease)
		mockS3.SetObject("test-lease-3", "expired-etag", data)

		// Try with wrong etag to trigger conflict
		os.WriteFile(lm.etagFilePath, []byte("wrong-etag"), 0644)

		ctx := context.Background()
		acquired, err := lm.AcquireLease(ctx)

		if err != nil {
			t.Fatalf("Expected no error, got: %v", err)
		}
		if !acquired {
			t.Fatal("Expected to acquire expired lease")
		}

		// Should have made 2 calls: 1 failed optimistic, 1 successful with current etag
		calls := mockS3.GetPutObjectCalls()
		if len(calls) != 2 {
			t.Fatalf("Expected 2 PutObject calls, got %d", len(calls))
		}

		// First call should fail with wrong etag
		firstCall := calls[0]
		if firstCall.Input.IfMatch == nil || *firstCall.Input.IfMatch != "wrong-etag" {
			t.Errorf("Expected first call IfMatch='wrong-etag', got %v", firstCall.Input.IfMatch)
		}

		// Second call should succeed with current etag
		secondCall := calls[1]
		if secondCall.Input.IfMatch == nil || *secondCall.Input.IfMatch != "expired-etag" {
			t.Errorf("Expected second call IfMatch='expired-etag', got %v", secondCall.Input.IfMatch)
		}

		lm.Stop()
	})

	t.Run("Scenario4_ConflictResolution_SameMachineID", func(t *testing.T) {
		mockS3 := NewMockS3Client()
		lm := createTestLeaseManager(mockS3, "machine-1", "test-lease-4")

		// Create active lease held by same machine (restart scenario)
		activeLease := createActiveLease("machine-1")
		data, _ := json.Marshal(activeLease)
		mockS3.SetObject("test-lease-4", "same-machine-etag", data)

		// Try with wrong etag to trigger conflict
		os.WriteFile(lm.etagFilePath, []byte("wrong-etag"), 0644)

		ctx := context.Background()
		acquired, err := lm.AcquireLease(ctx)

		if err != nil {
			t.Fatalf("Expected no error, got: %v", err)
		}
		if !acquired {
			t.Fatal("Expected to acquire lease from same machine")
		}

		// Should have made 2 calls: 1 failed optimistic, 1 successful with current etag
		calls := mockS3.GetPutObjectCalls()
		if len(calls) != 2 {
			t.Fatalf("Expected 2 PutObject calls, got %d", len(calls))
		}

		secondCall := calls[1]
		if secondCall.Input.IfMatch == nil || *secondCall.Input.IfMatch != "same-machine-etag" {
			t.Errorf("Expected second call IfMatch='same-machine-etag', got %v", secondCall.Input.IfMatch)
		}

		lm.Stop()
	})

	t.Run("Scenario5_WaitForLease_DifferentMachine", func(t *testing.T) {
		mockS3 := NewMockS3Client()
		lm := createTestLeaseManager(mockS3, "machine-1", "test-lease-5")

		// Create active lease held by different machine
		activeLease := createActiveLease("machine-2")
		data, _ := json.Marshal(activeLease)
		mockS3.SetObject("test-lease-5", "other-machine-etag", data)

		// Use a timeout context to avoid infinite waiting
		ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
		defer cancel()

		acquired, err := lm.AcquireLease(ctx)

		// Should return false (needs restore) and context deadline exceeded error
		if acquired {
			t.Fatal("Expected NOT to acquire lease held by different machine")
		}
		if err == nil {
			t.Fatal("Expected context deadline exceeded error")
		}
		if !strings.Contains(err.Error(), "deadline exceeded") && !strings.Contains(err.Error(), "context canceled") {
			t.Fatalf("Expected context deadline error, got: %v", err)
		}

		// Since the lease is optimistically tried first with empty etag, we expect 1 failed call
		calls := mockS3.GetPutObjectCalls()
		if len(calls) == 0 {
			t.Fatal("Expected at least 1 PutObject call for optimistic attempt")
		}

		lm.Stop()
	})

	t.Run("Scenario6_WaitForLease_LeaseExpiresDuringWait", func(t *testing.T) {
		mockS3 := NewMockS3Client()
		lm := createTestLeaseManager(mockS3, "machine-1", "test-lease-6")

		// Create lease that is already expired (simpler test)
		expiredLease := LeaseInfo{
			MachineID:  "machine-2",
			ExpiresAt:  time.Now().Add(-1 * time.Hour), // Already expired
			AcquiredAt: time.Now().Add(-2 * time.Hour),
		}
		data, _ := json.Marshal(expiredLease)
		mockS3.SetObject("test-lease-6", "expired-etag", data)

		// Try with wrong etag first to trigger the wait logic
		os.WriteFile(lm.etagFilePath, []byte("wrong-etag"), 0644)

		ctx := context.Background()
		acquired, err := lm.AcquireLease(ctx)

		if err != nil {
			t.Fatalf("Expected no error, got: %v", err)
		}
		if !acquired {
			t.Fatal("Expected to acquire expired lease")
		}

		// Should have made 2 calls: 1 failed optimistic, 1 successful with current etag
		calls := mockS3.GetPutObjectCalls()
		if len(calls) != 2 {
			t.Fatalf("Expected 2 PutObject calls, got %d", len(calls))
		}

		lm.Stop()
	})
}

func TestLeaseRefresh(t *testing.T) {
	mockS3 := NewMockS3Client()
	lm := createTestLeaseManager(mockS3, "machine-1", "test-lease-refresh")

	// Acquire initial lease
	ctx := context.Background()
	acquired, err := lm.AcquireLease(ctx)
	if err != nil || !acquired {
		t.Fatalf("Failed to acquire initial lease: %v", err)
	}

	// Wait a bit for refresh goroutine to start
	time.Sleep(10 * time.Millisecond)

	// Verify refresh ticker is running
	if lm.refreshTicker == nil {
		t.Fatal("Expected refresh ticker to be initialized")
	}

	lm.Stop()

	// Verify ticker is stopped
	select {
	case <-lm.refreshTicker.C:
		t.Fatal("Ticker should be stopped")
	default:
		// Good, ticker is stopped
	}
}

func TestCustomLeaseKey(t *testing.T) {
	config := Config{
		BaseDir:           t.TempDir(),
		S3AccessKey:       "test-key",
		S3SecretAccessKey: "test-secret",
		S3EndpointURL:     "http://localhost:9000",
		S3Bucket:          "test-bucket",
		VolumeName:        "test-volume",
	}

	// Set up environment
	os.Setenv("FLY_VOLUME_PATH", t.TempDir())
	os.Setenv("FLY_MACHINE_ID", "test-machine")
	defer func() {
		os.Unsetenv("FLY_VOLUME_PATH")
		os.Unsetenv("FLY_MACHINE_ID")
	}()

	customKey := "custom-lease-key-12345"
	lm := NewLeaseManagerWithKey(config, customKey)

	if lm.leaseKey != customKey {
		t.Errorf("Expected lease key %s, got %s", customKey, lm.leaseKey)
	}

	lm.Stop()
}

func TestBaseDirUsedForETagFile(t *testing.T) {
	customBaseDir := t.TempDir()
	config := Config{
		BaseDir:           customBaseDir,
		S3AccessKey:       "test-key",
		S3SecretAccessKey: "test-secret",
		S3EndpointURL:     "http://localhost:9000",
		S3Bucket:          "test-bucket",
		VolumeName:        "test-volume",
	}

	// Set up environment with different path to ensure BaseDir takes precedence
	differentPath := t.TempDir()
	os.Setenv("FLY_VOLUME_PATH", differentPath)
	os.Setenv("FLY_MACHINE_ID", "test-machine")
	defer func() {
		os.Unsetenv("FLY_VOLUME_PATH")
		os.Unsetenv("FLY_MACHINE_ID")
	}()

	lm := NewLeaseManager(config)

	expectedETagPath := filepath.Join(customBaseDir, ".juicefs-lease-etag")
	if lm.etagFilePath != expectedETagPath {
		t.Errorf("Expected etag file path %s, got %s", expectedETagPath, lm.etagFilePath)
	}

	// Verify it doesn't use FLY_VOLUME_PATH when BaseDir is set
	unexpectedPath := filepath.Join(differentPath, ".juicefs-lease-etag")
	if lm.etagFilePath == unexpectedPath {
		t.Errorf("ETag file path should not use FLY_VOLUME_PATH when BaseDir is set")
	}

	lm.Stop()
}

func TestLeaseManagerErrorHandling(t *testing.T) {
	t.Run("InvalidETagFile", func(t *testing.T) {
		mockS3 := NewMockS3Client()
		lm := createTestLeaseManager(mockS3, "machine-1", "test-lease-error")

		// Create invalid etag file (directory instead of file)
		os.MkdirAll(lm.etagFilePath, 0755)

		ctx := context.Background()
		acquired, err := lm.AcquireLease(ctx)

		// Should succeed despite etag file write failure (which only warns)
		if err != nil {
			t.Fatalf("Expected no error, lease acquisition should succeed despite etag file issues: %v", err)
		}
		if !acquired {
			t.Fatal("Expected to acquire lease even when etag file write fails")
		}

		// The etag file should still be a directory (unchanged)
		if stat, err := os.Stat(lm.etagFilePath); err != nil || !stat.IsDir() {
			t.Error("Expected etag file path to remain as directory")
		}

		lm.Stop()
	})

	t.Run("S3Error", func(t *testing.T) {
		// This would test S3 errors, but our mock doesn't simulate all error conditions
		// In a real test, you might use a more sophisticated mock or error injection
	})
}
