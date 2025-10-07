package db

import (
	"context"
	"testing"
)

func TestManagerConfig(t *testing.T) {
	cfg := Config{
		BaseDir: "/tmp/test",
		Logger:  nil, // Should get default logger
	}

	mgr, err := New(cfg)
	if err != nil {
		t.Fatal(err)
	}

	if mgr.config.BaseDir != "/tmp/test" {
		t.Errorf("expected base dir /tmp/test, got %s", mgr.config.BaseDir)
	}

	if mgr.logger == nil {
		t.Error("expected logger to be set")
	}

	// Without S3 config, leaser and litestream should be nil
	if mgr.leaser != nil {
		t.Error("expected leaser to be nil without S3 config")
	}
	if mgr.litestream != nil {
		t.Error("expected litestream to be nil without S3 config")
	}
}

func TestManagerWithS3(t *testing.T) {
	cfg := Config{
		BaseDir:           "/tmp/test",
		S3AccessKey:       "test-key",
		S3SecretAccessKey: "test-secret",
		S3EndpointURL:     "http://localhost:9000",
		S3Bucket:          "test-bucket",
		DatabasePaths:     []string{"/tmp/test.db"},
	}

	mgr, err := New(cfg)
	if err != nil {
		t.Fatal(err)
	}

	// With S3 config, leaser and litestream should be created
	if mgr.leaser == nil {
		t.Error("expected leaser to be created with S3 config")
	}
	if mgr.litestream == nil {
		t.Error("expected litestream to be created with S3 config and database paths")
	}
}

func TestManagerStartStop(t *testing.T) {
	cfg := Config{
		BaseDir: "/tmp/test",
	}

	mgr, err := New(cfg)
	if err != nil {
		t.Fatal(err)
	}

	ctx := context.Background()

	// Start should work even without leaser/litestream
	if err := mgr.Start(ctx); err != nil {
		t.Fatal(err)
	}

	if !mgr.started {
		t.Error("expected manager to be started")
	}

	// Stop should work
	if err := mgr.Stop(ctx); err != nil {
		t.Fatal(err)
	}

	if mgr.started {
		t.Error("expected manager to be stopped")
	}

	// Multiple stops should be safe
	if err := mgr.Stop(ctx); err != nil {
		t.Fatal(err)
	}
}

func TestAddDatabase(t *testing.T) {
	cfg := Config{
		BaseDir: "/tmp/test",
	}

	mgr, err := New(cfg)
	if err != nil {
		t.Fatal(err)
	}

	// Should be able to add databases before start
	if err := mgr.AddDatabase("/tmp/new.db"); err != nil {
		t.Fatal(err)
	}

	if len(mgr.config.DatabasePaths) != 1 {
		t.Errorf("expected 1 database path, got %d", len(mgr.config.DatabasePaths))
	}

	// Start the manager
	ctx := context.Background()
	if err := mgr.Start(ctx); err != nil {
		t.Fatal(err)
	}

	// Should not be able to add databases after start
	if err := mgr.AddDatabase("/tmp/another.db"); err == nil {
		t.Error("expected error adding database after start")
	}

	mgr.Stop(ctx)
}

func TestDatabasePath(t *testing.T) {
	cfg := Config{
		BaseDir: "/var/data",
	}

	mgr, err := New(cfg)
	if err != nil {
		t.Fatal(err)
	}

	path := mgr.DatabasePath("test.db")
	expected := "/var/data/test.db"
	if path != expected {
		t.Errorf("expected %s, got %s", expected, path)
	}
}

// Phase 1 Tests: Lifecycle behavior

func TestStartErrorsIfAlreadyStarted(t *testing.T) {
	cfg := Config{
		BaseDir: "/tmp/test",
	}

	mgr, err := New(cfg)
	if err != nil {
		t.Fatal(err)
	}
	defer CleanupTestDB(t, mgr)

	ctx := context.Background()

	// First Start should succeed
	if err := mgr.Start(ctx); err != nil {
		t.Fatal(err)
	}

	// Second Start should error
	if err := mgr.Start(ctx); err == nil {
		t.Error("expected error on second Start, got nil")
	}
}

func TestStopIsIdempotent(t *testing.T) {
	cfg := Config{
		BaseDir: "/tmp/test",
	}

	mgr, err := New(cfg)
	if err != nil {
		t.Fatal(err)
	}

	ctx := context.Background()

	// Start
	if err := mgr.Start(ctx); err != nil {
		t.Fatal(err)
	}

	// First Stop should succeed
	if err := mgr.Stop(ctx); err != nil {
		t.Fatalf("first Stop failed: %v", err)
	}

	// Second Stop should also succeed
	if err := mgr.Stop(ctx); err != nil {
		t.Fatalf("second Stop failed: %v", err)
	}

	// Third Stop should also succeed
	if err := mgr.Stop(ctx); err != nil {
		t.Fatalf("third Stop failed: %v", err)
	}
}

func TestRestartCycle(t *testing.T) {
	cfg := Config{
		BaseDir: "/tmp/test",
	}

	mgr, err := New(cfg)
	if err != nil {
		t.Fatal(err)
	}
	defer CleanupTestDB(t, mgr)

	ctx := context.Background()

	// First cycle
	if err := mgr.Start(ctx); err != nil {
		t.Fatalf("first Start failed: %v", err)
	}
	if err := mgr.Stop(ctx); err != nil {
		t.Fatalf("first Stop failed: %v", err)
	}

	// Second cycle
	if err := mgr.Start(ctx); err != nil {
		t.Fatalf("second Start failed: %v", err)
	}
	if err := mgr.Stop(ctx); err != nil {
		t.Fatalf("second Stop failed: %v", err)
	}

	// Third cycle
	if err := mgr.Start(ctx); err != nil {
		t.Fatalf("third Start failed: %v", err)
	}
	if err := mgr.Stop(ctx); err != nil {
		t.Fatalf("third Stop failed: %v", err)
	}
}

func TestChannelsClosed(t *testing.T) {
	cfg := Config{
		BaseDir: "/tmp/test",
	}

	mgr, err := New(cfg)
	if err != nil {
		t.Fatal(err)
	}

	ctx := context.Background()

	if err := mgr.Start(ctx); err != nil {
		t.Fatal(err)
	}
	if err := mgr.Stop(ctx); err != nil {
		t.Fatal(err)
	}

	// Check stopCh is closed
	select {
	case <-mgr.stopCh:
		// Good
	default:
		t.Error("stopCh not closed after Stop")
	}

	// Check stoppedCh is closed
	select {
	case <-mgr.stoppedCh:
		// Good
	default:
		t.Error("stoppedCh not closed after Stop")
	}
}

func TestVerifiersBeforeStart(t *testing.T) {
	cfg := Config{
		BaseDir: "/tmp/test",
	}

	mgr, err := New(cfg)
	if err != nil {
		t.Fatal(err)
	}

	// Before Start, verifiers should be empty
	if len(mgr.SetupVerifiers()) != 0 {
		t.Errorf("Expected 0 setup verifiers before Start, got %d", len(mgr.SetupVerifiers()))
	}
	if len(mgr.CleanupVerifiers()) != 0 {
		t.Errorf("Expected 0 cleanup verifiers before Start, got %d", len(mgr.CleanupVerifiers()))
	}
}

func TestVerifiersClearedOnRestart(t *testing.T) {
	cfg := Config{
		BaseDir: "/tmp/test",
	}

	mgr, err := New(cfg)
	if err != nil {
		t.Fatal(err)
	}
	defer CleanupTestDB(t, mgr)

	ctx := context.Background()

	// First start - no verifiers (no leaser/litestream)
	if err := mgr.Start(ctx); err != nil {
		t.Fatal(err)
	}
	firstSetupCount := len(mgr.SetupVerifiers())
	firstCleanupCount := len(mgr.CleanupVerifiers())

	if err := mgr.Stop(ctx); err != nil {
		t.Fatal(err)
	}

	// Second start - verifiers should be the same count (cleared and repopulated)
	if err := mgr.Start(ctx); err != nil {
		t.Fatal(err)
	}
	secondSetupCount := len(mgr.SetupVerifiers())
	secondCleanupCount := len(mgr.CleanupVerifiers())

	if firstSetupCount != secondSetupCount {
		t.Errorf("Setup verifier count changed on restart: %d -> %d", firstSetupCount, secondSetupCount)
	}
	if firstCleanupCount != secondCleanupCount {
		t.Errorf("Cleanup verifier count changed on restart: %d -> %d", firstCleanupCount, secondCleanupCount)
	}
}
