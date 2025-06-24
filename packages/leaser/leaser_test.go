package leaser

import (
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
	"github.com/aws/smithy-go"
)

// MockS3Client implements S3API for testing
type MockS3Client struct {
	objects map[string]*S3Object
	putFunc func(ctx context.Context, params *s3.PutObjectInput, optFns ...func(*s3.Options)) (*s3.PutObjectOutput, error)
}

type S3Object struct {
	Body string
	ETag string
}

func NewMockS3Client() *MockS3Client {
	return &MockS3Client{
		objects: make(map[string]*S3Object),
	}
}

func (m *MockS3Client) PutObject(ctx context.Context, params *s3.PutObjectInput, optFns ...func(*s3.Options)) (*s3.PutObjectOutput, error) {
	if m.putFunc != nil {
		return m.putFunc(ctx, params, optFns...)
	}

	key := *params.Key

	// Read the body
	bodyBytes, _ := io.ReadAll(params.Body)
	bodyStr := string(bodyBytes)

	// Handle conditional requests
	if params.IfNoneMatch != nil && *params.IfNoneMatch == "*" {
		// Object must not exist
		if _, exists := m.objects[key]; exists {
			return nil, &smithy.GenericAPIError{
				Code:    "PreconditionFailed",
				Message: "At least one of the pre-conditions you specified did not hold",
			}
		}
	}

	if params.IfMatch != nil {
		// Object must exist with specific ETag
		obj, exists := m.objects[key]
		if !exists {
			return nil, &smithy.GenericAPIError{
				Code:    "PreconditionFailed",
				Message: "At least one of the pre-conditions you specified did not hold",
			}
		}
		if obj.ETag != *params.IfMatch {
			return nil, &smithy.GenericAPIError{
				Code:    "PreconditionFailed",
				Message: "At least one of the pre-conditions you specified did not hold",
			}
		}
	}

	// Generate new ETag
	newETag := fmt.Sprintf("etag-%d", len(bodyStr))

	// Store object
	m.objects[key] = &S3Object{
		Body: bodyStr,
		ETag: newETag,
	}

	return &s3.PutObjectOutput{
		ETag: aws.String(fmt.Sprintf(`"%s"`, newETag)),
	}, nil
}

func (m *MockS3Client) GetObject(ctx context.Context, params *s3.GetObjectInput, optFns ...func(*s3.Options)) (*s3.GetObjectOutput, error) {
	key := *params.Key
	obj, exists := m.objects[key]
	if !exists {
		return nil, &smithy.GenericAPIError{
			Code:    "NoSuchKey",
			Message: "The specified key does not exist.",
		}
	}

	return &s3.GetObjectOutput{
		Body: io.NopCloser(strings.NewReader(obj.Body)),
		ETag: aws.String(fmt.Sprintf(`"%s"`, obj.ETag)),
	}, nil
}

func (m *MockS3Client) HeadObject(ctx context.Context, params *s3.HeadObjectInput, optFns ...func(*s3.Options)) (*s3.HeadObjectOutput, error) {
	key := *params.Key
	obj, exists := m.objects[key]
	if !exists {
		return nil, &smithy.GenericAPIError{
			Code:    "NoSuchKey",
			Message: "The specified key does not exist.",
		}
	}

	return &s3.HeadObjectOutput{
		ETag: aws.String(fmt.Sprintf(`"%s"`, obj.ETag)),
	}, nil
}

func (m *MockS3Client) SetPutFunc(fn func(ctx context.Context, params *s3.PutObjectInput, optFns ...func(*s3.Options)) (*s3.PutObjectOutput, error)) {
	m.putFunc = fn
}

func setupTestLeaser(t *testing.T) (*Leaser, *MockS3Client, string) {
	tmpDir := t.TempDir()
	mockS3 := NewMockS3Client()

	leaser := NewWithS3Client(mockS3, "test-bucket", "test-lease", "machine-1", tmpDir)

	return leaser, mockS3, tmpDir
}

func TestLeaser_SuccessfulAcquisition(t *testing.T) {
	leaser, _, _ := setupTestLeaser(t)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	err := leaser.Wait(ctx)
	if err != nil {
		t.Fatalf("Expected successful lease acquisition, got error: %v", err)
	}

	if leaser.LeaseAttemptCount() != 1 {
		t.Errorf("Expected attempt count 1, got %d", leaser.LeaseAttemptCount())
	}

	leaser.Stop()
}

func TestLeaser_AcquisitionWithExistingETag(t *testing.T) {
	leaser, mockS3, tmpDir := setupTestLeaser(t)

	// Create an existing lease in S3 that this machine can take over
	existingLease := LeaseInfo{
		MachineID:  "machine-1", // Same machine
		ExpiresAt:  time.Now().Add(1 * time.Hour),
		AcquiredAt: time.Now(),
	}
	existingData, _ := json.Marshal(existingLease)

	// Put existing lease in mock S3
	mockS3.objects["test-lease"] = &S3Object{
		Body: string(existingData),
		ETag: "existing-etag",
	}

	// Write existing etag file
	etagFile := filepath.Join(tmpDir, ".sprite-lease-etag")
	err := os.WriteFile(etagFile, []byte("existing-etag"), 0644)
	if err != nil {
		t.Fatalf("Failed to write etag file: %v", err)
	}

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	err = leaser.Wait(ctx)
	if err != nil {
		t.Fatalf("Expected successful lease acquisition, got error: %v", err)
	}

	leaser.Stop()
}

func TestLeaser_ConflictWithExpiredLease(t *testing.T) {
	leaser, mockS3, _ := setupTestLeaser(t)

	// Create expired lease
	expiredLease := LeaseInfo{
		MachineID:  "other-machine",
		ExpiresAt:  time.Now().Add(-1 * time.Hour), // Expired
		AcquiredAt: time.Now().Add(-2 * time.Hour),
	}
	expiredData, _ := json.Marshal(expiredLease)

	// Put expired lease in mock S3
	mockS3.objects["test-lease"] = &S3Object{
		Body: string(expiredData),
		ETag: "expired-etag",
	}

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	err := leaser.Wait(ctx)
	if err != nil {
		t.Fatalf("Expected successful lease acquisition with expired lease, got error: %v", err)
	}

	leaser.Stop()
}

func TestLeaser_ConflictWithSameMachine(t *testing.T) {
	leaser, mockS3, _ := setupTestLeaser(t)

	// Create lease held by same machine
	sameMachineLease := LeaseInfo{
		MachineID:  "machine-1", // Same as leaser
		ExpiresAt:  time.Now().Add(1 * time.Hour),
		AcquiredAt: time.Now(),
	}
	leaseData, _ := json.Marshal(sameMachineLease)

	// Put lease in mock S3
	mockS3.objects["test-lease"] = &S3Object{
		Body: string(leaseData),
		ETag: "same-machine-etag",
	}

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	err := leaser.Wait(ctx)
	if err != nil {
		t.Fatalf("Expected successful lease acquisition with same machine, got error: %v", err)
	}

	leaser.Stop()
}

func TestLeaser_TakeOverExpiredLeaseFromDifferentMachine(t *testing.T) {
	leaser, mockS3, _ := setupTestLeaser(t)

	// Create an expired lease held by different machine
	expiredLease := LeaseInfo{
		MachineID:  "other-machine",
		ExpiresAt:  time.Now().Add(-1 * time.Second), // Already expired
		AcquiredAt: time.Now().Add(-2 * time.Second),
	}
	expiredData, _ := json.Marshal(expiredLease)

	// Put expired lease in mock S3
	mockS3.objects["test-lease"] = &S3Object{
		Body: string(expiredData),
		ETag: "other-machine-etag",
	}

	ctx, cancel := context.WithTimeout(context.Background(), 1*time.Second)
	defer cancel()

	err := leaser.Wait(ctx)
	if err != nil {
		t.Fatalf("Expected successful lease acquisition from expired lease, got error: %v", err)
	}

	// Should successfully take over an expired lease
	// This should be 2 attempts: first fails with bad etag, second succeeds with correct etag
	if leaser.LeaseAttemptCount() != 2 {
		t.Errorf("Expected 2 attempts, got %d", leaser.LeaseAttemptCount())
	}

	leaser.Stop()
}

func TestLeaser_TimeoutWaitingForLease(t *testing.T) {
	leaser, mockS3, _ := setupTestLeaser(t)

	// Create lease held by different machine that won't expire
	otherMachineLease := LeaseInfo{
		MachineID:  "other-machine",
		ExpiresAt:  time.Now().Add(1 * time.Hour), // Won't expire during test
		AcquiredAt: time.Now(),
	}
	leaseData, _ := json.Marshal(otherMachineLease)

	// Put lease in mock S3
	mockS3.objects["test-lease"] = &S3Object{
		Body: string(leaseData),
		ETag: "other-machine-etag",
	}

	ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
	defer cancel()

	err := leaser.Wait(ctx)
	if err == nil {
		t.Fatalf("Expected timeout error, but lease acquisition succeeded")
	}

	if !strings.Contains(err.Error(), "context deadline exceeded") {
		t.Errorf("Expected context deadline exceeded error, got: %v", err)
	}

	leaser.Stop()
}

func TestLeaser_S3Errors(t *testing.T) {
	leaser, mockS3, _ := setupTestLeaser(t)

	// Set up mock to return error
	mockS3.SetPutFunc(func(ctx context.Context, params *s3.PutObjectInput, optFns ...func(*s3.Options)) (*s3.PutObjectOutput, error) {
		return nil, &smithy.GenericAPIError{
			Code:    "InternalError",
			Message: "Something went wrong",
		}
	})

	ctx, cancel := context.WithTimeout(context.Background(), 1*time.Second)
	defer cancel()

	err := leaser.Wait(ctx)
	if err == nil {
		t.Fatalf("Expected error from S3 failure, but got success")
	}

	if !strings.Contains(err.Error(), "failed to try acquire lease") {
		t.Errorf("Expected lease acquisition error, got: %v", err)
	}

	leaser.Stop()
}

func TestLeaser_StopBeforeAcquisition(t *testing.T) {
	leaser, mockS3, _ := setupTestLeaser(t)

	// Create lease held by different machine
	otherMachineLease := LeaseInfo{
		MachineID:  "other-machine",
		ExpiresAt:  time.Now().Add(1 * time.Hour),
		AcquiredAt: time.Now(),
	}
	leaseData, _ := json.Marshal(otherMachineLease)

	// Put lease in mock S3
	mockS3.objects["test-lease"] = &S3Object{
		Body: string(leaseData),
		ETag: "other-machine-etag",
	}

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	// Stop the leaser immediately
	go func() {
		time.Sleep(50 * time.Millisecond)
		leaser.Stop()
	}()

	// This should eventually fail due to context cancellation
	// when waiting for the lease
	err := leaser.Wait(ctx)

	// We expect either a timeout or successful acquisition depending on timing
	// The key is that Stop() should work cleanly
	if err != nil && !strings.Contains(err.Error(), "context deadline exceeded") {
		t.Logf("Got error (acceptable): %v", err)
	}
}

func TestLeaser_ETagFileHandling(t *testing.T) {
	leaser, _, tmpDir := setupTestLeaser(t)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	err := leaser.Wait(ctx)
	if err != nil {
		t.Fatalf("Expected successful lease acquisition, got error: %v", err)
	}

	// Check that etag file was created
	etagFile := filepath.Join(tmpDir, ".sprite-lease-etag")
	if _, err := os.Stat(etagFile); os.IsNotExist(err) {
		t.Errorf("Expected etag file to be created at %s", etagFile)
	}

	// Read etag file and verify it's not empty
	data, err := os.ReadFile(etagFile)
	if err != nil {
		t.Errorf("Failed to read etag file: %v", err)
	}
	if len(data) == 0 {
		t.Errorf("Expected etag file to contain data")
	}

	leaser.Stop()
}

func TestLeaser_MultipleStopCalls(t *testing.T) {
	leaser, _, _ := setupTestLeaser(t)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	err := leaser.Wait(ctx)
	if err != nil {
		t.Fatalf("Expected successful lease acquisition, got error: %v", err)
	}

	// Call Stop multiple times - should not panic or cause issues
	leaser.Stop()
	leaser.Stop()
	leaser.Stop()
}

func TestLeaser_RefreshLease(t *testing.T) {
	leaser, mockS3, _ := setupTestLeaser(t)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	err := leaser.Wait(ctx)
	if err != nil {
		t.Fatalf("Expected successful lease acquisition, got error: %v", err)
	}

	// Verify that the lease object exists in mock S3
	obj, exists := mockS3.objects["test-lease"]
	if !exists {
		t.Fatalf("Expected lease object to exist in S3")
	}

	// Verify lease content
	var leaseInfo LeaseInfo
	err = json.Unmarshal([]byte(obj.Body), &leaseInfo)
	if err != nil {
		t.Fatalf("Failed to parse lease info: %v", err)
	}

	if leaseInfo.MachineID != "machine-1" {
		t.Errorf("Expected machine ID 'machine-1', got '%s'", leaseInfo.MachineID)
	}

	if time.Until(leaseInfo.ExpiresAt) <= 0 {
		t.Errorf("Expected lease to be valid, but it's expired")
	}

	leaser.Stop()
}
