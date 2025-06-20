package lib

import (
	"encoding/json"
	"fmt"
	"log/slog"
	"os"
	"strings"
	"time"
)

// ConfigLoader handles loading configuration from JSON files with environment variable substitution
type ConfigLoader struct{}

// NewConfigLoader creates a new ConfigLoader
func NewConfigLoader() *ConfigLoader {
	return &ConfigLoader{}
}

// LoadFromFile loads configuration from a JSON file with environment variable substitution
func (cl *ConfigLoader) LoadFromFile(filename string) (*ApplicationConfig, error) {
	data, err := os.ReadFile(filename)
	if err != nil {
		return nil, fmt.Errorf("failed to read config file: %w", err)
	}

	// Parse JSON into raw map first to handle env var substitution
	var rawConfig map[string]interface{}
	if err := json.Unmarshal(data, &rawConfig); err != nil {
		return nil, fmt.Errorf("failed to parse JSON: %w", err)
	}

	// Perform environment variable substitution
	substituted := cl.substituteEnvVars(rawConfig)

	// Marshal back to JSON for structured parsing
	substitutedJSON, err := json.Marshal(substituted)
	if err != nil {
		return nil, fmt.Errorf("failed to marshal substituted config: %w", err)
	}

	// Parse into structured config
	var config JSONConfig
	if err := json.Unmarshal(substitutedJSON, &config); err != nil {
		return nil, fmt.Errorf("failed to parse config structure: %w", err)
	}

	// Convert JSONConfig to ApplicationConfig
	return config.ToApplicationConfig()
}

// substituteEnvVars recursively substitutes environment variables in the config map
func (cl *ConfigLoader) substituteEnvVars(value interface{}) interface{} {
	switch v := value.(type) {
	case map[string]interface{}:
		// Check if this is an env var reference
		if envVar, ok := v["$env"].(string); ok && len(v) == 1 {
			// This is an environment variable reference
			if envValue := os.Getenv(envVar); envValue != "" {
				return envValue
			}
			// Return empty string if env var not set
			return ""
		}

		// Otherwise, recurse into the map
		result := make(map[string]interface{})
		for key, val := range v {
			result[key] = cl.substituteEnvVars(val)
		}
		return result

	case []interface{}:
		// Recurse into arrays
		result := make([]interface{}, len(v))
		for i, val := range v {
			result[i] = cl.substituteEnvVars(val)
		}
		return result

	default:
		// Return other types as-is
		return value
	}
}

// JSONConfig represents the JSON configuration structure
type JSONConfig struct {
	// Logging configuration
	LogLevel string `json:"log_level,omitempty"`
	LogJSON  bool   `json:"log_json,omitempty"`
	Debug    bool   `json:"debug,omitempty"`

	// API Server configuration
	APIListenAddr string `json:"api_listen_addr,omitempty"`

	// Components configuration (keyed by component name)
	Components map[string]JSONComponentScripts `json:"components,omitempty"`

	// Process configuration
	ProcessCommand                 []string `json:"process_command,omitempty"`
	ProcessWorkingDir              string   `json:"process_working_dir,omitempty"`
	ProcessEnvironment             []string `json:"process_environment,omitempty"`
	ProcessRestartMaxRetries       int      `json:"process_restart_max_retries,omitempty"`
	ProcessRestartBackoffMax       string   `json:"process_restart_backoff_max,omitempty"`
	ProcessGracefulShutdownTimeout string   `json:"process_graceful_shutdown_timeout,omitempty"`

	// S3 configuration
	S3 *S3Config `json:"s3,omitempty"`

	// Exec configuration
	Exec *ExecConfig `json:"exec,omitempty"`
}

// JSONComponentScripts represents component scripts in JSON format
type JSONComponentScripts struct {
	StartCommand      []string `json:"start_command,omitempty"`
	ReadyCommand      []string `json:"ready_command,omitempty"`
	CheckpointCommand []string `json:"checkpoint_command,omitempty"`
	RestoreCommand    []string `json:"restore_command,omitempty"`
}

// ToApplicationConfig converts JSONConfig to ApplicationConfig
func (jc *JSONConfig) ToApplicationConfig() (*ApplicationConfig, error) {
	config := &ApplicationConfig{
		LogJSON:                  jc.LogJSON,
		Debug:                    jc.Debug,
		APIListenAddr:            jc.APIListenAddr,
		ProcessCommand:           jc.ProcessCommand,
		ProcessWorkingDir:        jc.ProcessWorkingDir,
		ProcessEnvironment:       jc.ProcessEnvironment,
		ProcessRestartMaxRetries: jc.ProcessRestartMaxRetries,
	}

	// Parse log level
	if jc.LogLevel != "" {
		switch strings.ToLower(jc.LogLevel) {
		case "debug":
			config.LogLevel = slog.LevelDebug
		case "info":
			config.LogLevel = slog.LevelInfo
		case "warn", "warning":
			config.LogLevel = slog.LevelWarn
		case "error":
			config.LogLevel = slog.LevelError
		default:
			return nil, fmt.Errorf("invalid log level: %s", jc.LogLevel)
		}
	} else {
		config.LogLevel = slog.LevelInfo
	}

	// Parse durations
	if jc.ProcessRestartBackoffMax != "" {
		duration, err := time.ParseDuration(jc.ProcessRestartBackoffMax)
		if err != nil {
			return nil, fmt.Errorf("invalid process_restart_backoff_max: %w", err)
		}
		config.ProcessRestartBackoffMax = duration
	} else {
		config.ProcessRestartBackoffMax = 60 * time.Second
	}

	if jc.ProcessGracefulShutdownTimeout != "" {
		duration, err := time.ParseDuration(jc.ProcessGracefulShutdownTimeout)
		if err != nil {
			return nil, fmt.Errorf("invalid process_graceful_shutdown_timeout: %w", err)
		}
		config.ProcessGracefulShutdownTimeout = duration
	} else {
		config.ProcessGracefulShutdownTimeout = 30 * time.Second
	}

	// Convert components
	if jc.Components != nil {
		config.Components = make(map[string]ComponentScripts)
		for name, scripts := range jc.Components {
			config.Components[name] = ComponentScripts{
				StartCommand:      scripts.StartCommand,
				ReadyCommand:      scripts.ReadyCommand,
				CheckpointCommand: scripts.CheckpointCommand,
				RestoreCommand:    scripts.RestoreCommand,
			}
		}
	}

	// Copy S3 config if present
	if jc.S3 != nil {
		config.S3 = *jc.S3
	}

	// Copy Exec config if present
	if jc.Exec != nil {
		config.Exec = *jc.Exec
	}

	return config, nil
}
