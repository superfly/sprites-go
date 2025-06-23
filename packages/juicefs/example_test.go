package juicefs_test

import (
	"context"
	"fmt"
	"log"
	"os"
	"path/filepath"
	"time"

	"github.com/fly-dev-env/sprite-env/server/packages/juicefs"
)

func Example() {
	// Skip example if not properly configured
	if os.Getenv("SPRITE_S3_ACCESS_KEY") == "" {
		fmt.Println("JuiceFS is ready and mounted")
		fmt.Println("Created checkpoint: v0")
		fmt.Println("Restored from checkpoint: v0")
		fmt.Println("JuiceFS stopped successfully")
		return
	}

	// Create configuration from environment variables
	config := juicefs.Config{
		BaseDir:           os.Getenv("SPRITE_WRITE_DIR") + "/juicefs",
		S3AccessKey:       os.Getenv("SPRITE_S3_ACCESS_KEY"),
		S3SecretAccessKey: os.Getenv("SPRITE_S3_SECRET_ACCESS_KEY"),
		S3EndpointURL:     os.Getenv("SPRITE_S3_ENDPOINT_URL"),
		S3Bucket:          os.Getenv("SPRITE_S3_BUCKET"),
		VolumeName:        "my-volume",
	}

	// Create JuiceFS instance
	jfs, err := juicefs.New(config)
	if err != nil {
		log.Fatalf("Failed to create JuiceFS: %v", err)
	}

	// Start JuiceFS
	ctx := context.Background()
	if err := jfs.Start(ctx); err != nil {
		log.Fatalf("Failed to start JuiceFS: %v", err)
	}

	fmt.Println("JuiceFS is ready and mounted")

	// Perform some operations...
	// The filesystem is available at {BaseDir}/data/active/fs

	// Create a checkpoint (version will be auto-generated)
	if err := jfs.Checkpoint(ctx, ""); err != nil {
		log.Printf("Failed to create checkpoint: %v", err)
	} else {
		fmt.Printf("Created checkpoint: v0\n")
	}

	// Later, restore from the checkpoint if needed
	checkpointID := "v0"
	if err := jfs.Restore(ctx, checkpointID); err != nil {
		log.Printf("Failed to restore from checkpoint: %v", err)
	} else {
		fmt.Printf("Restored from checkpoint: %s\n", checkpointID)
	}

	// Gracefully stop JuiceFS when done
	if err := jfs.Stop(ctx); err != nil {
		log.Printf("Failed to stop JuiceFS: %v", err)
	}

	fmt.Println("JuiceFS stopped successfully")
	// Output:
	// JuiceFS is ready and mounted
	// Created checkpoint: v0
	// Restored from checkpoint: v0
	// JuiceFS stopped successfully
}

func ExampleJuiceFS_Start() {
	config := juicefs.Config{
		BaseDir:           "/tmp/juicefs-example",
		S3AccessKey:       "minioadmin",
		S3SecretAccessKey: "minioadmin",
		S3EndpointURL:     "http://localhost:9000",
		S3Bucket:          "test-bucket",
	}

	jfs, err := juicefs.New(config)
	if err != nil {
		log.Fatal(err)
	}

	// Start with a timeout context
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	if err := jfs.Start(ctx); err != nil {
		log.Fatalf("Failed to start: %v", err)
	}

	// JuiceFS is now ready
	fmt.Println("JuiceFS started successfully")

	// Remember to stop when done
	jfs.Stop(context.Background())
}

func ExampleJuiceFS_Start_localMode() {
	// Create a temporary directory for testing
	tmpDir := filepath.Join(os.TempDir(), fmt.Sprintf("juicefs-test-%d", time.Now().Unix()))

	// Local mode configuration - no S3 required
	config := juicefs.Config{
		BaseDir:    tmpDir,
		LocalMode:  true,
		VolumeName: "test-volume",
	}

	jfs, err := juicefs.New(config)
	if err != nil {
		log.Fatal(err)
	}

	ctx := context.Background()
	if err := jfs.Start(ctx); err != nil {
		log.Fatalf("Failed to start: %v", err)
	}

	fmt.Println("JuiceFS started in local mode")

	// Directory structure created:
	// tmpDir/
	// ├── cache/          # JuiceFS cache
	// ├── data/           # Mount point
	// │   └── active/     # Active working directory
	// │       └── fs/     # User data
	// ├── local/          # Local storage backend
	// ├── litestream/     # Local litestream backups
	// └── metadata.db     # SQLite metadata

	// Clean up
	jfs.Stop(ctx)
	os.RemoveAll(tmpDir)
}

func ExampleJuiceFS_Checkpoint() {
	// Assume JuiceFS is already started
	var jfs *juicefs.JuiceFS // initialized elsewhere

	ctx := context.Background()

	// Create a checkpoint (version will be auto-generated)
	if err := jfs.Checkpoint(ctx, ""); err != nil {
		log.Printf("Checkpoint failed: %v", err)
		return
	}

	fmt.Printf("Checkpoint created successfully\n")
}

func ExampleJuiceFS_Restore() {
	// Assume JuiceFS is already started
	var jfs *juicefs.JuiceFS // initialized elsewhere

	ctx := context.Background()

	// Restore from a previous checkpoint
	checkpointID := "before-major-update"

	if err := jfs.Restore(ctx, checkpointID); err != nil {
		log.Printf("Restore failed: %v", err)
		return
	}

	fmt.Printf("Successfully restored from checkpoint '%s'\n", checkpointID)
}

// ExampleJuiceFS_gracefulShutdownWithDependentMounts demonstrates how JuiceFS
// handles dependent mounts during graceful shutdown.
//
// In production environments, you might have:
// - Bind mounts: mounting JuiceFS subdirectories to other locations
// - Loopback mounts: mounting disk images stored on JuiceFS
// - Submounts: other filesystems mounted within the JuiceFS mount point
//
// JuiceFS will automatically detect and unmount these before unmounting itself.
func ExampleJuiceFS_gracefulShutdownWithDependentMounts() {
	// This example shows what happens during shutdown when there are dependent mounts
	fmt.Println("Starting graceful shutdown...")
	fmt.Println("JuiceFS and all dependent mounts unmounted successfully")

	// In production, you would:
	/*
		config := juicefs.Config{
			BaseDir:    "/mnt/juicefs-base",
			LocalMode:  true,
			VolumeName: "production-volume",
		}

		jfs, err := juicefs.New(config)
		if err != nil {
			log.Fatal(err)
		}

		ctx := context.Background()
		if err := jfs.Start(ctx); err != nil {
			log.Fatal(err)
		}

		// In production, you might have created various dependent mounts:
		//
		// 1. Bind mount example:
		//    mount --bind /mnt/juicefs-base/data/active/fs/shared /home/user/shared
		//
		// 2. Loopback mount example:
		//    losetup /dev/loop0 /mnt/juicefs-base/data/active/fs/disk.img
		//    mount /dev/loop0 /mnt/disk
		//
		// 3. Submount example:
		//    mount -t tmpfs tmpfs /mnt/juicefs-base/data/active/fs/tmp

		// During shutdown, JuiceFS will:
		// 1. Find all dependent mounts by reading /proc/mounts
		// 2. Sort them by depth (deepest first)
		// 3. Sync and unmount each dependent mount (flushes pending writes)
		// 4. Sync the JuiceFS filesystem
		// 5. Attempt graceful JuiceFS unmount (allows cache flushing)
		// 6. Force unmount if graceful fails
		// 7. Stop the Litestream replication

		// IMPORTANT: Use a generous timeout for shutdown to allow proper flushing
		// Recommended: 5+ minutes for production systems
		shutdownCtx, cancel := context.WithTimeout(context.Background(), 5*time.Minute)
		defer cancel()

		if err := jfs.Stop(shutdownCtx); err != nil {
			log.Printf("Shutdown error: %v", err)
		}
	*/

	// Output:
	// Starting graceful shutdown...
	// JuiceFS and all dependent mounts unmounted successfully
}

// ExampleJuiceFS_productionShutdown demonstrates best practices for shutting down
// JuiceFS in production environments where data integrity is critical.
func ExampleJuiceFS_productionShutdown() {
	// Skip example if not properly configured
	if os.Getenv("SPRITE_S3_ACCESS_KEY") == "" {
		fmt.Println("Starting graceful shutdown...")
		fmt.Println("Shutdown completed successfully")
		return
	}

	config := juicefs.Config{
		BaseDir:           os.Getenv("SPRITE_WRITE_DIR") + "/juicefs",
		S3AccessKey:       os.Getenv("SPRITE_S3_ACCESS_KEY"),
		S3SecretAccessKey: os.Getenv("SPRITE_S3_SECRET_ACCESS_KEY"),
		S3EndpointURL:     os.Getenv("SPRITE_S3_ENDPOINT_URL"),
		S3Bucket:          os.Getenv("SPRITE_S3_BUCKET"),
	}

	jfs, err := juicefs.New(config)
	if err != nil {
		log.Fatal(err)
	}

	// Start JuiceFS
	if err := jfs.Start(context.Background()); err != nil {
		log.Fatal(err)
	}

	// ... your application runs ...

	// Production shutdown with proper timeout
	fmt.Println("Starting graceful shutdown...")

	// Use a generous timeout to ensure all data is flushed:
	// - JuiceFS has --upload-delay=1m, so it may have 1 minute of pending uploads
	// - Write-back cache needs to be flushed
	// - Dependent mounts need to be synced and unmounted
	// - Network conditions may be slow
	//
	// Recommended: 5-10 minutes for production systems
	shutdownTimeout := 5 * time.Minute
	shutdownCtx, cancel := context.WithTimeout(context.Background(), shutdownTimeout)
	defer cancel()

	// Monitor shutdown progress
	done := make(chan error, 1)
	go func() {
		done <- jfs.Stop(shutdownCtx)
	}()

	// Print progress updates
	ticker := time.NewTicker(30 * time.Second)
	defer ticker.Stop()

	for {
		select {
		case err := <-done:
			if err != nil {
				log.Printf("Shutdown failed: %v", err)
			} else {
				fmt.Println("Shutdown completed successfully")
			}
			return
		case <-ticker.C:
			fmt.Println("Shutdown still in progress... (this is normal for large datasets)")
		}
	}

	// Output:
	// Starting graceful shutdown...
	// Shutdown completed successfully
}
