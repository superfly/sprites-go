package juicefs

import (
    "bytes"
    "context"
    "io"
    "log/slog"
    "os"
    "path/filepath"
    "testing"
    "time"
)

func TestControlFlushDoesNotError(t *testing.T) {
	if os.Getenv("SPRITE_TEST_DOCKER") != "1" {
		t.Fatal("This test must run in the Docker test environment (SPRITE_TEST_DOCKER=1)")
	}

	// Ensure expected binaries are present in the Docker image
	if _, err := os.Stat("/usr/local/bin/juicefs"); err != nil {
		t.Fatal("juicefs not found in PATH - Docker test environment is misconfigured")
	}
	if _, err := os.Stat("/usr/local/bin/litestream"); err != nil {
		t.Fatal("litestream not found in PATH - Docker test environment is misconfigured")
	}

	tempDir := t.TempDir()

	logger := slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{Level: slog.LevelDebug}))

	cfg := Config{
		BaseDir:     tempDir,
		LocalMode:   true,
		VolumeName:  "test-control-flush",
		Logger:      logger,
		UploadDelay: 2 * time.Minute,
	}

	jfs, err := New(cfg)
	if err != nil {
		t.Fatalf("Failed to create JuiceFS: %v", err)
	}

	ctx := context.Background()
	if err := jfs.Start(ctx); err != nil {
		t.Fatalf("Failed to start JuiceFS: %v", err)
	}
	defer func() {
		stopCtx, cancel := context.WithTimeout(context.Background(), 5*time.Minute)
		defer cancel()
		if err := jfs.Stop(stopCtx); err != nil {
			t.Errorf("Failed to stop JuiceFS: %v", err)
		}
	}()

    // Write some non-zero files under the mounted filesystem (upload-delay=2m)
	mountPath := jfs.GetMountPath()
	dataDir := filepath.Join(mountPath, "active", "fs")
	if err := os.MkdirAll(dataDir, 0755); err != nil {
		t.Fatalf("failed to ensure data directory: %v", err)
	}

	payload := bytes.Repeat([]byte("A"), 1024*256) // 256 KiB
	for i := 0; i < 5; i++ {
		name := filepath.Join(dataDir, "file-"+time.Now().Format("150405.000000000")+"-"+string(rune('a'+i)))
		if err := os.WriteFile(name, payload, 0644); err != nil {
			t.Fatalf("failed to write test file: %v", err)
		}
		// small delay to vary timestamps
		time.Sleep(10 * time.Millisecond)
	}

    // Locate the rawstaging directory under cache (retry as it is created after mount activity)
    cacheDir := filepath.Join(tempDir, "cache")
    var rawstaging string
    findDeadline := time.Now().Add(30 * time.Second)
    for time.Now().Before(findDeadline) {
        if p, err := findRawstagingDir(cacheDir); err == nil {
            rawstaging = p
            break
        }
        time.Sleep(200 * time.Millisecond)
    }
    if rawstaging == "" {
        t.Fatal("failed to locate rawstaging directory under cache within timeout")
    }

    // Ensure there is at least one staged file to flush (retry briefly, recursive scan)
    hasStaged := false
    stagedDeadline := time.Now().Add(15 * time.Second)
    for time.Now().Before(stagedDeadline) {
        hasStaged = false
        _ = filepath.WalkDir(rawstaging, func(path string, d os.DirEntry, err error) error {
            if err != nil {
                return nil
            }
            if d.IsDir() {
                return nil
            }
            name := filepath.Base(path)
            if !isIgnoredWritebackFile(name) {
                hasStaged = true
                return io.EOF // early stop walk
            }
            return nil
        })
        if hasStaged {
            break
        }
        time.Sleep(100 * time.Millisecond)
    }
    if !hasStaged {
        t.Fatal("expected staged files in rawstaging before flush, found none")
    }

	// Verify control file exists
	controlPath := filepath.Join(mountPath, ".control")
	if _, err := os.Stat(controlPath); err != nil {
		t.Fatalf("control file not present at %s: %v", controlPath, err)
	}

	// Invoke the control-file flush and expect no error
	if err := jfs.flushCacheViaControl(controlPath); err != nil {
		t.Fatalf("flushCacheViaControl returned error: %v", err)
	}

    // After FlushNow, staged chunks should drain; poll rawstaging recursively until empty
    drainDeadline := time.Now().Add(2 * time.Minute)
    for time.Now().Before(drainDeadline) {
        any := false
        _ = filepath.WalkDir(rawstaging, func(path string, d os.DirEntry, err error) error {
            if err != nil {
                return nil
            }
            if d.IsDir() {
                return nil
            }
            name := filepath.Base(path)
            if !isIgnoredWritebackFile(name) {
                any = true
                return io.EOF
            }
            return nil
        })
        if !any {
            break
        }
        time.Sleep(200 * time.Millisecond)
    }
}
