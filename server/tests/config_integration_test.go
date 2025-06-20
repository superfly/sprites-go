package tests

import (
	"encoding/json"
	"log/slog"
	"os"
	"path/filepath"
	"testing"

	"lib"
)

func TestConfigLoading(t *testing.T) {
	// Create a temporary directory for test files
	tmpDir, err := os.MkdirTemp("", "sprite-env-config-test")
	if err != nil {
		t.Fatal(err)
	}
	defer os.RemoveAll(tmpDir)

	t.Run("basic config loading", func(t *testing.T) {
		configFile := filepath.Join(tmpDir, "basic.json")
		config := map[string]interface{}{
			"log_level":                         "debug",
			"api_listen_addr":                   ":9090",
			"process_command":                   []string{"echo", "hello"},
			"process_graceful_shutdown_timeout": "10s",
		}

		if err := writeJSONFile(configFile, config); err != nil {
			t.Fatal(err)
		}

		loader := lib.NewConfigLoader()
		loaded, err := loader.LoadFromFile(configFile)
		if err != nil {
			t.Fatalf("Failed to load config: %v", err)
		}

		if loaded.LogLevel != slog.LevelDebug {
			t.Errorf("Expected log level DEBUG, got %v", loaded.LogLevel)
		}
		if loaded.APIListenAddr != ":9090" {
			t.Errorf("Expected API listen addr :9090, got %s", loaded.APIListenAddr)
		}
		if len(loaded.ProcessCommand) != 2 || loaded.ProcessCommand[0] != "echo" {
			t.Errorf("Unexpected process command: %v", loaded.ProcessCommand)
		}
		if loaded.ProcessGracefulShutdownTimeout.Seconds() != 10 {
			t.Errorf("Expected 10s shutdown timeout, got %v", loaded.ProcessGracefulShutdownTimeout)
		}
	})

	t.Run("environment variable substitution", func(t *testing.T) {
		// Set test environment variables
		os.Setenv("TEST_S3_ACCESS", "access-key-123")
		os.Setenv("TEST_S3_SECRET", "secret-key-456")
		os.Setenv("TEST_S3_ENDPOINT", "https://s3.test.com")
		defer func() {
			os.Unsetenv("TEST_S3_ACCESS")
			os.Unsetenv("TEST_S3_SECRET")
			os.Unsetenv("TEST_S3_ENDPOINT")
		}()

		configFile := filepath.Join(tmpDir, "env.json")
		config := map[string]interface{}{
			"s3": map[string]interface{}{
				"access_key": map[string]string{"$env": "TEST_S3_ACCESS"},
				"secret_key": map[string]string{"$env": "TEST_S3_SECRET"},
				"endpoint":   map[string]string{"$env": "TEST_S3_ENDPOINT"},
			},
		}

		if err := writeJSONFile(configFile, config); err != nil {
			t.Fatal(err)
		}

		loader := lib.NewConfigLoader()
		loaded, err := loader.LoadFromFile(configFile)
		if err != nil {
			t.Fatalf("Failed to load config: %v", err)
		}

		if loaded.S3.AccessKey != "access-key-123" {
			t.Errorf("Expected S3 access key 'access-key-123', got %s", loaded.S3.AccessKey)
		}
		if loaded.S3.SecretKey != "secret-key-456" {
			t.Errorf("Expected S3 secret key 'secret-key-456', got %s", loaded.S3.SecretKey)
		}
		if loaded.S3.Endpoint != "https://s3.test.com" {
			t.Errorf("Expected S3 endpoint 'https://s3.test.com', got %s", loaded.S3.Endpoint)
		}
	})

	t.Run("unset environment variable", func(t *testing.T) {
		// Ensure env var is not set
		os.Unsetenv("UNSET_VAR")

		configFile := filepath.Join(tmpDir, "unset.json")
		config := map[string]interface{}{
			"s3": map[string]interface{}{
				"access_key": map[string]string{"$env": "UNSET_VAR"},
			},
		}

		if err := writeJSONFile(configFile, config); err != nil {
			t.Fatal(err)
		}

		loader := lib.NewConfigLoader()
		loaded, err := loader.LoadFromFile(configFile)
		if err != nil {
			t.Fatalf("Failed to load config: %v", err)
		}

		if loaded.S3.AccessKey != "" {
			t.Errorf("Expected empty string for unset env var, got %s", loaded.S3.AccessKey)
		}
	})

	t.Run("exec wrapper configuration", func(t *testing.T) {
		configFile := filepath.Join(tmpDir, "exec.json")
		config := map[string]interface{}{
			"exec": map[string]interface{}{
				"wrapper_command":     []string{"crun", "exec", "app"},
				"tty_wrapper_command": []string{"crun", "exec", "-t", "app"},
			},
		}

		if err := writeJSONFile(configFile, config); err != nil {
			t.Fatal(err)
		}

		loader := lib.NewConfigLoader()
		loaded, err := loader.LoadFromFile(configFile)
		if err != nil {
			t.Fatalf("Failed to load config: %v", err)
		}

		if len(loaded.Exec.WrapperCommand) != 3 || loaded.Exec.WrapperCommand[0] != "crun" {
			t.Errorf("Unexpected wrapper command: %v", loaded.Exec.WrapperCommand)
		}
		if len(loaded.Exec.TTYWrapperCommand) != 4 || loaded.Exec.TTYWrapperCommand[2] != "-t" {
			t.Errorf("Unexpected TTY wrapper command: %v", loaded.Exec.TTYWrapperCommand)
		}
	})

	t.Run("components configuration", func(t *testing.T) {
		configFile := filepath.Join(tmpDir, "components.json")
		config := map[string]interface{}{
			"components": map[string]interface{}{
				"db": map[string]interface{}{
					"start_command": []string{"/scripts/db/start.sh"},
					"ready_command": []string{"/scripts/db/ready.sh"},
				},
				"cache": map[string]interface{}{
					"start_command":      []string{"/scripts/cache/start.sh"},
					"checkpoint_command": []string{"/scripts/cache/checkpoint.sh"},
				},
			},
		}

		if err := writeJSONFile(configFile, config); err != nil {
			t.Fatal(err)
		}

		loader := lib.NewConfigLoader()
		loaded, err := loader.LoadFromFile(configFile)
		if err != nil {
			t.Fatalf("Failed to load config: %v", err)
		}

		if len(loaded.Components) != 2 {
			t.Errorf("Expected 2 components, got %d", len(loaded.Components))
		}

		db, ok := loaded.Components["db"]
		if !ok {
			t.Error("Missing 'db' component")
		} else {
			if len(db.StartCommand) != 1 || db.StartCommand[0] != "/scripts/db/start.sh" {
				t.Errorf("Unexpected db start command: %v", db.StartCommand)
			}
			if len(db.ReadyCommand) != 1 || db.ReadyCommand[0] != "/scripts/db/ready.sh" {
				t.Errorf("Unexpected db ready command: %v", db.ReadyCommand)
			}
		}

		cache, ok := loaded.Components["cache"]
		if !ok {
			t.Error("Missing 'cache' component")
		} else {
			if len(cache.StartCommand) != 1 || cache.StartCommand[0] != "/scripts/cache/start.sh" {
				t.Errorf("Unexpected cache start command: %v", cache.StartCommand)
			}
			if len(cache.CheckpointCommand) != 1 || cache.CheckpointCommand[0] != "/scripts/cache/checkpoint.sh" {
				t.Errorf("Unexpected cache checkpoint command: %v", cache.CheckpointCommand)
			}
		}
	})

	t.Run("complex nested env substitution", func(t *testing.T) {
		os.Setenv("TEST_PORT", "8080")
		os.Setenv("TEST_HOST", "localhost")
		defer func() {
			os.Unsetenv("TEST_PORT")
			os.Unsetenv("TEST_HOST")
		}()

		configFile := filepath.Join(tmpDir, "nested.json")
		config := map[string]interface{}{
			"api_listen_addr": map[string]string{"$env": "TEST_HOST"},
			"process_environment": []interface{}{
				"HOST=myhost",
				map[string]string{"$env": "TEST_PORT"},
			},
		}

		if err := writeJSONFile(configFile, config); err != nil {
			t.Fatal(err)
		}

		loader := lib.NewConfigLoader()
		loaded, err := loader.LoadFromFile(configFile)
		if err != nil {
			t.Fatalf("Failed to load config: %v", err)
		}

		// Note: The api_listen_addr will be "localhost" because the whole value is replaced
		if loaded.APIListenAddr != "localhost" {
			t.Errorf("Expected API listen addr 'localhost', got %s", loaded.APIListenAddr)
		}

		// Check array env substitution
		if len(loaded.ProcessEnvironment) != 2 {
			t.Errorf("Expected 2 environment entries, got %d", len(loaded.ProcessEnvironment))
		} else {
			if loaded.ProcessEnvironment[0] != "HOST=myhost" {
				t.Errorf("Expected first env 'HOST=myhost', got %s", loaded.ProcessEnvironment[0])
			}
			if loaded.ProcessEnvironment[1] != "8080" {
				t.Errorf("Expected second env '8080', got %s", loaded.ProcessEnvironment[1])
			}
		}
	})

	t.Run("invalid config file", func(t *testing.T) {
		configFile := filepath.Join(tmpDir, "invalid.json")
		if err := os.WriteFile(configFile, []byte(`{invalid json`), 0644); err != nil {
			t.Fatal(err)
		}

		loader := lib.NewConfigLoader()
		_, err := loader.LoadFromFile(configFile)
		if err == nil {
			t.Error("Expected error loading invalid JSON")
		}
	})

	t.Run("non-existent config file", func(t *testing.T) {
		loader := lib.NewConfigLoader()
		_, err := loader.LoadFromFile(filepath.Join(tmpDir, "does-not-exist.json"))
		if err == nil {
			t.Error("Expected error loading non-existent file")
		}
	})
}

// Helper function to write JSON config files
func writeJSONFile(path string, data interface{}) error {
	jsonBytes, err := json.MarshalIndent(data, "", "  ")
	if err != nil {
		return err
	}
	return os.WriteFile(path, jsonBytes, 0644)
}
