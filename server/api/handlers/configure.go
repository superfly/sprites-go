package handlers

import (
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"time"
)

// ConfigureRequest represents the JSON request for configuration
// The request body should be a JSON object with environment variable names as keys
// Example: { "SPRITE_S3_ACCESS_KEY": "value", "SPRITE_S3_BUCKET": "mybucket" }
type ConfigureRequest map[string]string

// HandleConfigure handles dynamic configuration requests
func (h *Handlers) HandleConfigure(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// Check if system is already configured
	if h.system.IsConfigured() {
		http.Error(w, "System already configured", http.StatusBadRequest)
		return
	}

	// Read request body
	body, err := io.ReadAll(r.Body)
	if err != nil {
		h.logger.Error("Failed to read request body", "error", err)
		http.Error(w, "Failed to read request body", http.StatusBadRequest)
		return
	}

	// Parse request
	var req ConfigureRequest
	if err := json.Unmarshal(body, &req); err != nil {
		h.logger.Error("Failed to parse JSON", "error", err)
		http.Error(w, "Invalid JSON", http.StatusBadRequest)
		return
	}

	// Get the dynamic config path
	configPath := h.system.GetDynamicConfigPath()
	if configPath == "" {
		http.Error(w, "Dynamic configuration not enabled", http.StatusBadRequest)
		return
	}

	// Build system config from environment variables
	config, err := h.buildSystemConfigFromEnv(req)
	if err != nil {
		h.logger.Error("Failed to build configuration", "error", err)
		http.Error(w, fmt.Sprintf("Invalid configuration: %v", err), http.StatusBadRequest)
		return
	}

	// Configure the system
	if err := h.system.Configure(config); err != nil {
		h.logger.Error("Failed to configure system", "error", err)
		http.Error(w, fmt.Sprintf("Failed to configure system: %v", err), http.StatusInternalServerError)
		return
	}

	// Boot the system
	if err := h.system.Boot(r.Context()); err != nil {
		h.logger.Error("Failed to boot system", "error", err)
		// If boot fails, we should exit the process as requested
		// First, try to delete the config file
		if configPath != "" {
			os.Remove(configPath)
		}
		// Exit with code 1
		go func() {
			time.Sleep(100 * time.Millisecond) // Give time for response to be sent
			os.Exit(1)
		}()
		http.Error(w, fmt.Sprintf("Failed to boot system: %v", err), http.StatusInternalServerError)
		return
	}

	// Persist configuration to file
	if err := h.persistConfig(configPath, req); err != nil {
		h.logger.Error("Failed to persist configuration", "error", err)
		// Continue anyway since system is already configured
	}

	h.logger.Info("System configured and booted successfully")
	w.WriteHeader(http.StatusOK)
	w.Write([]byte(`{"status": "configured"}`))
}

// configData holds the configuration data we'll pass to Configure
type configData struct {
	// Process configuration
	ProcessCommand                 []string
	ProcessWorkingDir              string
	ProcessEnvironment             []string
	ProcessGracefulShutdownTimeout time.Duration

	// Container configuration
	ContainerEnabled    bool
	ContainerSocketDir  string
	ContainerTTYTimeout time.Duration

	// JuiceFS configuration
	JuiceFSBaseDir    string
	JuiceFSLocalMode  bool
	S3AccessKey       string
	S3SecretAccessKey string
	S3EndpointURL     string
	S3Bucket          string

	// Overlay configuration
	OverlayEnabled       bool
	OverlayImageSize     string
	OverlayLowerPath     string
	OverlayTargetPath    string
	OverlaySkipOverlayFS bool
}

// buildSystemConfigFromEnv builds configuration from environment variables
// It merges actual environment variables with the provided overrides
func (h *Handlers) buildSystemConfigFromEnv(overrides map[string]string) (configData, error) {
	var config configData

	// Helper to get value with override priority
	getEnv := func(key string) string {
		if val, ok := overrides[key]; ok {
			return val
		}
		return os.Getenv(key)
	}

	// Process configuration
	if cmd := getEnv("SPRITE_PROCESS_CMD"); cmd != "" {
		// Parse command (simple space-separated for now)
		// TODO: This is a simple implementation - may need proper shell parsing
		parts := strings.Fields(cmd)
		if len(parts) > 0 {
			config.ProcessCommand = parts
		}
	}
	config.ProcessWorkingDir = getEnv("SPRITE_PROCESS_WORKDIR")
	
	// Process environment - collect all SPRITE_PROCESS_ENV_* variables
	// First from actual environment
	for _, envVar := range os.Environ() {
		if strings.HasPrefix(envVar, "SPRITE_PROCESS_ENV_") {
			parts := strings.SplitN(envVar, "=", 2)
			if len(parts) == 2 {
				envName := strings.TrimPrefix(parts[0], "SPRITE_PROCESS_ENV_")
				config.ProcessEnvironment = append(config.ProcessEnvironment, fmt.Sprintf("%s=%s", envName, parts[1]))
			}
		}
	}
	// Then override with provided values
	for k, v := range overrides {
		if strings.HasPrefix(k, "SPRITE_PROCESS_ENV_") {
			envName := strings.TrimPrefix(k, "SPRITE_PROCESS_ENV_")
			// Check if we need to update existing or add new
			found := false
			for i, existing := range config.ProcessEnvironment {
				if strings.HasPrefix(existing, envName+"=") {
					config.ProcessEnvironment[i] = fmt.Sprintf("%s=%s", envName, v)
					found = true
					break
				}
			}
			if !found {
				config.ProcessEnvironment = append(config.ProcessEnvironment, fmt.Sprintf("%s=%s", envName, v))
			}
		}
	}

	// Container configuration
	config.ContainerEnabled = getEnv("SPRITE_CONTAINER_ENABLED") == "true"
	config.ContainerSocketDir = getEnv("SPRITE_CONTAINER_SOCKET_DIR")
	if timeout := getEnv("SPRITE_CONTAINER_TTY_TIMEOUT"); timeout != "" {
		if d, err := time.ParseDuration(timeout); err == nil {
			config.ContainerTTYTimeout = d
		}
	}

	// JuiceFS configuration
	if writeDir := getEnv("SPRITE_WRITE_DIR"); writeDir != "" {
		config.JuiceFSBaseDir = filepath.Join(writeDir, "juicefs")
	}
	config.JuiceFSLocalMode = getEnv("SPRITE_JUICEFS_LOCAL_MODE") == "true"
	config.S3AccessKey = getEnv("SPRITE_S3_ACCESS_KEY")
	config.S3SecretAccessKey = getEnv("SPRITE_S3_SECRET_ACCESS_KEY")
	config.S3EndpointURL = getEnv("SPRITE_S3_ENDPOINT_URL")
	config.S3Bucket = getEnv("SPRITE_S3_BUCKET")

	// Overlay configuration
	overlayEnabled := getEnv("SPRITE_OVERLAY_ENABLED")
	if overlayEnabled == "true" {
		config.OverlayEnabled = true
	} else if overlayEnabled == "false" {
		config.OverlayEnabled = false
	}
	config.OverlayImageSize = getEnv("SPRITE_OVERLAY_IMAGE_SIZE")
	config.OverlayLowerPath = getEnv("SPRITE_OVERLAY_LOWER_PATH")
	config.OverlayTargetPath = getEnv("SPRITE_OVERLAY_TARGET_PATH")
	skipOverlayFS := getEnv("SPRITE_OVERLAY_SKIP_OVERLAYFS")
	if skipOverlayFS == "true" {
		config.OverlaySkipOverlayFS = true
	} else if skipOverlayFS == "false" {
		config.OverlaySkipOverlayFS = false
	}

	// Graceful shutdown timeout
	if timeout := getEnv("SPRITE_GRACEFUL_SHUTDOWN_TIMEOUT"); timeout != "" {
		if d, err := time.ParseDuration(timeout); err == nil {
			config.ProcessGracefulShutdownTimeout = d
		}
	} else {
		config.ProcessGracefulShutdownTimeout = 30 * time.Second
	}

	return config, nil
}

// persistConfig persists the complete configuration to a file
// It merges actual environment variables with the provided overrides
func (h *Handlers) persistConfig(path string, overrides map[string]string) error {
	// Ensure directory exists
	dir := filepath.Dir(path)
	if err := os.MkdirAll(dir, 0755); err != nil {
		return fmt.Errorf("failed to create directory: %w", err)
	}

	// Helper to get value with override priority
	getEnv := func(key string) string {
		if val, ok := overrides[key]; ok {
			return val
		}
		return os.Getenv(key)
	}

	// Convert environment to config file format
	fileConfig := make(map[string]interface{})

	// Map environment variables to config file fields
	if val := getEnv("SPRITE_LOG_LEVEL"); val != "" {
		fileConfig["log_level"] = val
	}
	if val := getEnv("SPRITE_LOG_JSON"); val == "true" {
		fileConfig["log_json"] = true
	}
	if val := getEnv("SPRITE_HTTP_API_LISTEN"); val != "" {
		fileConfig["api_listen_addr"] = val
	}
	if val := getEnv("SPRITE_PROCESS_CMD"); val != "" {
		// Parse command to array
		parts := strings.Fields(val)
		if len(parts) > 0 {
			fileConfig["process_command"] = parts
		}
	}
	if val := getEnv("SPRITE_PROCESS_WORKDIR"); val != "" {
		fileConfig["process_working_dir"] = val
	}
	
	// Process environment variables - merge actual env with overrides
	var processEnv []string
	processedKeys := make(map[string]bool)
	
	// First from actual environment
	for _, envVar := range os.Environ() {
		if strings.HasPrefix(envVar, "SPRITE_PROCESS_ENV_") {
			parts := strings.SplitN(envVar, "=", 2)
			if len(parts) == 2 {
				key := parts[0]
				envName := strings.TrimPrefix(key, "SPRITE_PROCESS_ENV_")
				// Check if there's an override
				if overrideVal, hasOverride := overrides[key]; hasOverride {
					processEnv = append(processEnv, fmt.Sprintf("%s=%s", envName, overrideVal))
					processedKeys[key] = true
				} else {
					processEnv = append(processEnv, fmt.Sprintf("%s=%s", envName, parts[1]))
				}
			}
		}
	}
	
	// Then add any override-only values
	for k, v := range overrides {
		if strings.HasPrefix(k, "SPRITE_PROCESS_ENV_") && !processedKeys[k] {
			envName := strings.TrimPrefix(k, "SPRITE_PROCESS_ENV_")
			processEnv = append(processEnv, fmt.Sprintf("%s=%s", envName, v))
		}
	}
	
	if len(processEnv) > 0 {
		fileConfig["process_environment"] = processEnv
	}

	// Container configuration
	if val := getEnv("SPRITE_CONTAINER_ENABLED"); val == "true" {
		fileConfig["container_enabled"] = true
	} else if val == "false" {
		fileConfig["container_enabled"] = false
	}
	if val := getEnv("SPRITE_CONTAINER_SOCKET_DIR"); val != "" {
		fileConfig["container_socket_dir"] = val
	}
	if val := getEnv("SPRITE_CONTAINER_TTY_TIMEOUT"); val != "" {
		fileConfig["container_tty_timeout"] = val
	}

	// JuiceFS configuration
	if val := getEnv("SPRITE_WRITE_DIR"); val != "" {
		fileConfig["juicefs_base_dir"] = filepath.Join(val, "juicefs")
	}
	if val := getEnv("SPRITE_JUICEFS_LOCAL_MODE"); val == "true" {
		fileConfig["juicefs_local_mode"] = true
	} else if val == "false" {
		fileConfig["juicefs_local_mode"] = false
	}
	if val := getEnv("SPRITE_S3_ACCESS_KEY"); val != "" {
		fileConfig["s3_access_key"] = val
	}
	if val := getEnv("SPRITE_S3_SECRET_ACCESS_KEY"); val != "" {
		fileConfig["s3_secret_access_key"] = val
	}
	if val := getEnv("SPRITE_S3_ENDPOINT_URL"); val != "" {
		fileConfig["s3_endpoint_url"] = val
	}
	if val := getEnv("SPRITE_S3_BUCKET"); val != "" {
		fileConfig["s3_bucket"] = val
	}

	// Overlay configuration
	if val := getEnv("SPRITE_OVERLAY_ENABLED"); val == "true" {
		fileConfig["overlay_enabled"] = true
	} else if val == "false" {
		fileConfig["overlay_enabled"] = false
	}
	if val := getEnv("SPRITE_OVERLAY_IMAGE_SIZE"); val != "" {
		fileConfig["overlay_image_size"] = val
	}
	if val := getEnv("SPRITE_OVERLAY_LOWER_PATH"); val != "" {
		fileConfig["overlay_lower_path"] = val
	}
	if val := getEnv("SPRITE_OVERLAY_TARGET_PATH"); val != "" {
		fileConfig["overlay_target_path"] = val
	}
	if val := getEnv("SPRITE_OVERLAY_SKIP_OVERLAYFS"); val == "true" {
		fileConfig["overlay_skip_overlayfs"] = true
	} else if val == "false" {
		fileConfig["overlay_skip_overlayfs"] = false
	}

	// Marshal to JSON
	data, err := json.MarshalIndent(fileConfig, "", "  ")
	if err != nil {
		return fmt.Errorf("failed to marshal config: %w", err)
	}

	// Write to file
	if err := os.WriteFile(path, data, 0644); err != nil {
		return fmt.Errorf("failed to write config file: %w", err)
	}

	return nil
}