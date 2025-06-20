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

	// Create a checkpoint after some work
	checkpointID := fmt.Sprintf("checkpoint-%d", time.Now().Unix())
	if err := jfs.Checkpoint(ctx, checkpointID); err != nil {
		log.Printf("Failed to create checkpoint: %v", err)
	} else {
		fmt.Printf("Created checkpoint: %s\n", checkpointID)
	}

	// Later, restore from the checkpoint if needed
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
	// Created checkpoint: checkpoint-1234567890
	// Restored from checkpoint: checkpoint-1234567890
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

	// Create a checkpoint with a descriptive name
	checkpointID := "before-major-update"

	if err := jfs.Checkpoint(ctx, checkpointID); err != nil {
		log.Printf("Checkpoint failed: %v", err)
		return
	}

	fmt.Printf("Checkpoint '%s' created successfully\n", checkpointID)
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
