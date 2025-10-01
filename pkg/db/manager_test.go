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
