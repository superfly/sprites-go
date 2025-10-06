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

	err := leaser.Start(ctx)
	if err != nil {
		t.Fatalf("Expected successful lease acquisition, got error: %v", err)
	}

	if leaser.LeaseAttemptCount() != 1 {
		t.Errorf("Expected attempt count 1, got %d", leaser.LeaseAttemptCount())
	}

	if err := leaser.Stop(ctx); err != nil {
		t.Fatalf("Stop failed: %v", err)
	}
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

	err = leaser.Start(ctx)
	if err != nil {
		t.Fatalf("Expected successful lease acquisition, got error: %v", err)
	}

	if err := leaser.Stop(ctx); err != nil {
		t.Fatalf("Stop failed: %v", err)
	}
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

	err := leaser.Start(ctx)
	if err != nil {
		t.Fatalf("Expected successful lease acquisition with expired lease, got error: %v", err)
	}

	if err := leaser.Stop(ctx); err != nil {
		t.Fatalf("Stop failed: %v", err)
	}
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

	err := leaser.Start(ctx)
	if err != nil {
		t.Fatalf("Expected successful lease acquisition with same machine, got error: %v", err)
	}

	if err := leaser.Stop(ctx); err != nil {
		t.Fatalf("Stop failed: %v", err)
	}
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

	err := leaser.Start(ctx)
	if err != nil {
		t.Fatalf("Expected successful lease acquisition from expired lease, got error: %v", err)
	}

	// Should successfully take over an expired lease
	// This should be 2 attempts: first fails with bad etag, second succeeds with correct etag
	if leaser.LeaseAttemptCount() != 2 {
		t.Errorf("Expected 2 attempts, got %d", leaser.LeaseAttemptCount())
	}

	if err := leaser.Stop(ctx); err != nil {
		t.Fatalf("Stop failed: %v", err)
	}
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

	err := leaser.Start(ctx)
	if err == nil {
		t.Fatalf("Expected timeout error, but lease acquisition succeeded")
	}

	if !strings.Contains(err.Error(), "context deadline exceeded") {
		t.Errorf("Expected context deadline exceeded error, got: %v", err)
	}

	stopCtx := context.Background()
	if err := leaser.Stop(stopCtx); err != nil {
		t.Fatalf("Stop failed: %v", err)
	}
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

	err := leaser.Start(ctx)
	if err == nil {
		t.Fatalf("Expected error from S3 failure, but got success")
	}

	if !strings.Contains(err.Error(), "failed to try acquire lease") {
		t.Errorf("Expected lease acquisition error, got: %v", err)
	}

	stopCtx := context.Background()
	if err := leaser.Stop(stopCtx); err != nil {
		t.Fatalf("Stop failed: %v", err)
	}
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

	stopCtx := context.Background()

	// Stop the leaser immediately
	go func() {
		time.Sleep(50 * time.Millisecond)
		if err := leaser.Stop(stopCtx); err != nil {
			t.Logf("Stop error: %v", err)
		}
	}()

	// This should eventually fail due to context cancellation
	// when waiting for the lease
	err := leaser.Start(ctx)

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

	err := leaser.Start(ctx)
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

	if err := leaser.Stop(ctx); err != nil {
		t.Fatalf("Stop failed: %v", err)
	}
}

func TestLeaser_MultipleStopCalls(t *testing.T) {
	leaser, _, _ := setupTestLeaser(t)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	err := leaser.Start(ctx)
	if err != nil {
		t.Fatalf("Expected successful lease acquisition, got error: %v", err)
	}

	// Call Stop multiple times - should not panic or cause issues
	if err := leaser.Stop(ctx); err != nil {
		t.Fatalf("First Stop failed: %v", err)
	}
	if err := leaser.Stop(ctx); err != nil {
		t.Fatalf("Second Stop failed: %v", err)
	}
	if err := leaser.Stop(ctx); err != nil {
		t.Fatalf("Third Stop failed: %v", err)
	}
}

func TestLeaser_RefreshLease(t *testing.T) {
	leaser, mockS3, _ := setupTestLeaser(t)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	err := leaser.Start(ctx)
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

	if err := leaser.Stop(ctx); err != nil {
		t.Fatalf("Stop failed: %v", err)
	}
}

// Phase 1 Tests: Idempotency and Restartability

func TestLeaser_MultipleStartCalls(t *testing.T) {
	leaser, _, _ := setupTestLeaser(t)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	// First Start should succeed
	err := leaser.Start(ctx)
	if err != nil {
		t.Fatalf("First Start failed: %v", err)
	}

	// Second Start should error (already started)
	err = leaser.Start(ctx)
	if err == nil {
		t.Fatal("Second Start should have failed with 'already started' error")
	}
	if !strings.Contains(err.Error(), "already started") {
		t.Errorf("Expected 'already started' error, got: %v", err)
	}

	// Third Start should also error
	err = leaser.Start(ctx)
	if err == nil {
		t.Fatal("Third Start should have failed with 'already started' error")
	}

	// Should only have attempted once
	if leaser.LeaseAttemptCount() != 1 {
		t.Errorf("Expected 1 attempt, got %d", leaser.LeaseAttemptCount())
	}

	if err := leaser.Stop(ctx); err != nil {
		t.Fatalf("Stop failed: %v", err)
	}
}

func TestLeaser_RestartCycle(t *testing.T) {
	leaser, _, _ := setupTestLeaser(t)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	// First cycle: Start → Stop
	err := leaser.Start(ctx)
	if err != nil {
		t.Fatalf("First Start failed: %v", err)
	}

	if err := leaser.Stop(ctx); err != nil {
		t.Fatalf("First Stop failed: %v", err)
	}

	// Second cycle: Start → Stop (should work after restart)
	err = leaser.Start(ctx)
	if err != nil {
		t.Fatalf("Second Start (after restart) failed: %v", err)
	}

	if err := leaser.Stop(ctx); err != nil {
		t.Fatalf("Second Stop failed: %v", err)
	}

	// Third cycle to be sure
	err = leaser.Start(ctx)
	if err != nil {
		t.Fatalf("Third Start (after restart) failed: %v", err)
	}

	if err := leaser.Stop(ctx); err != nil {
		t.Fatalf("Third Stop failed: %v", err)
	}
}

func TestLeaser_WaitMethod(t *testing.T) {
	leaser, _, _ := setupTestLeaser(t)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	// Start the leaser
	err := leaser.Start(ctx)
	if err != nil {
		t.Fatalf("Start failed: %v", err)
	}

	// Stop it in a goroutine
	go func() {
		time.Sleep(100 * time.Millisecond)
		if err := leaser.Stop(ctx); err != nil {
			t.Logf("Stop error: %v", err)
		}
	}()

	// Wait() should block until Stop() completes
	err = leaser.Wait()
	if err != nil {
		t.Fatalf("Wait returned error: %v", err)
	}
}

// Phase 2 Tests: Verification

func TestLeaser_VerifySetup(t *testing.T) {
	leaser, _, _ := setupTestLeaser(t)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	// Should have no verifiers before Start
	if len(leaser.SetupVerifiers()) != 0 {
		t.Error("Should have no verifiers before Start()")
	}

	// Start the leaser
	if err := leaser.Start(ctx); err != nil {
		t.Fatalf("Start failed: %v", err)
	}

	// Should have setup verifiers and they should pass
	verifiers := leaser.SetupVerifiers()
	if len(verifiers) == 0 {
		t.Fatal("Expected setup verifiers after Start, got none")
	}

	for i, verify := range verifiers {
		if err := verify(ctx); err != nil {
			t.Errorf("Setup verifier %d failed: %v", i, err)
		}
	}

	// Cleanup
	if err := leaser.Stop(ctx); err != nil {
		t.Fatalf("Stop failed: %v", err)
	}
}

func TestLeaser_VerifyCleanup(t *testing.T) {
	leaser, _, _ := setupTestLeaser(t)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	// Start and stop
	if err := leaser.Start(ctx); err != nil {
		t.Fatalf("Start failed: %v", err)
	}

	if err := leaser.Stop(ctx); err != nil {
		t.Fatalf("Stop failed: %v", err)
	}

	// Run all cleanup verifiers
	verifiers := leaser.CleanupVerifiers()
	for i, verify := range verifiers {
		if err := verify(ctx); err != nil {
			t.Errorf("Cleanup verifier %d failed: %v", i, err)
		}
	}
}

func TestLeaser_Verifiers(t *testing.T) {
	leaser, _, _ := setupTestLeaser(t)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	// Before Start, should have no verifiers
	if len(leaser.SetupVerifiers()) != 0 {
		t.Errorf("Expected 0 setup verifiers before Start, got %d", len(leaser.SetupVerifiers()))
	}
	if len(leaser.CleanupVerifiers()) != 0 {
		t.Errorf("Expected 0 cleanup verifiers before Start, got %d", len(leaser.CleanupVerifiers()))
	}

	// Start the leaser
	if err := leaser.Start(ctx); err != nil {
		t.Fatalf("Start failed: %v", err)
	}

	// After Start, should have verifiers
	setupVerifiers := leaser.SetupVerifiers()
	cleanupVerifiers := leaser.CleanupVerifiers()
	if len(setupVerifiers) == 0 {
		t.Error("Expected setup verifiers after Start, got none")
	}
	if len(cleanupVerifiers) == 0 {
		t.Error("Expected cleanup verifiers after Start, got none")
	}

	// Run setup verifiers - should pass
	for i, verify := range setupVerifiers {
		if err := verify(ctx); err != nil {
			t.Errorf("Setup verifier %d failed: %v", i, err)
		}
	}

	// Cleanup
	if err := leaser.Stop(ctx); err != nil {
		t.Fatalf("Stop failed: %v", err)
	}

	// Run cleanup verifiers - should pass
	for i, verify := range cleanupVerifiers {
		if err := verify(ctx); err != nil {
			t.Errorf("Cleanup verifier %d failed: %v", i, err)
		}
	}
}

func TestLeaser_TestHelpers(t *testing.T) {
	leaser, _, _ := setupTestLeaser(t)

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	// Start the leaser
	if err := leaser.Start(ctx); err != nil {
		t.Fatalf("Start failed: %v", err)
	}

	// Use test helper to cleanup
	CleanupTestLeaser(t, leaser)
}

func TestMapFlyRegionToTigris(t *testing.T) {
	tests := []struct {
		name     string
		input    string
		expected string
	}{
		// Special cases
		{"Empty string", "", ""},
		{"Auto region", "auto", ""},

		// Direct mappings
		{"Amsterdam", "ams", "ams"},
		{"Chicago", "ord", "ord"},
		{"Dallas", "dfw", "dfw"},
		{"Frankfurt", "fra", "fra"},
		{"Ashburn", "iad", "iad"},
		{"London", "lhr", "lhr"},
		{"Newark", "ewr", "ewr"},
		{"Sao Paulo", "gru", "gru"},
		{"Singapore", "sin", "sin"},
		{"San Jose", "sjc", "sjc"},
		{"Sydney", "syd", "syd"},
		{"Tokyo", "nrt", "nrt"},
		{"Johannesburg", "jnb", "jnb"},

		// Geographical mappings
		{"Los Angeles to San Jose", "lax", "sjc"},
		{"Seattle to San Jose", "sea", "sjc"},
		{"Toronto to Chicago", "yyz", "ord"},
		{"Boston to Newark", "bos", "ewr"},
		{"Atlanta to Ashburn", "atl", "iad"},
		{"Paris to Frankfurt", "cdg", "fra"},
		{"Hong Kong to Singapore", "hkg", "sin"},
		{"Buenos Aires to Sao Paulo", "eze", "gru"},
		{"Melbourne to Sydney", "mel", "syd"},
		{"Dubai to Johannesburg", "dxb", "jnb"},

		// Unknown region
		{"Unknown region", "xyz", ""},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := MapFlyRegionToTigris(tt.input)
			if result != tt.expected {
				t.Errorf("MapFlyRegionToTigris(%q) = %q, want %q", tt.input, result, tt.expected)
			}
		})
	}
}
