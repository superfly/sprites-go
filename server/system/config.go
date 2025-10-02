package system

import (
	"encoding/json"
	"flag"
	"fmt"
	"log/slog"
	"os"
	"path/filepath"
	"strings"
	"time"
)

// Config holds all application configuration
type Config struct {
	// Logging
	LogLevel slog.Level
	LogJSON  bool
	Debug    bool

	// API Server
	APIListenAddr string
	APIToken      string
	AdminToken    string // Optional admin-specific token

	// Process
	ProcessCommand                 []string
	ProcessWorkingDir              string
	ProcessEnvironment             []string
	ProcessGracefulShutdownTimeout time.Duration

	// JuiceFS
	JuiceFSBaseDir    string
	JuiceFSLocalMode  bool
	S3AccessKey       string
	S3SecretAccessKey string
	S3EndpointURL     string
	S3Bucket          string

	// Exec
	ExecWrapperCommand []string

	// Debug
	KeepAliveOnError bool // Keep server running when process fails
	WaitForBoot      bool // Wait for SIGUSR1 before starting

	// Overlay configuration
	OverlayEnabled       bool     // Enable root overlay mounting
	OverlayImageSize     string   // Size of the overlay image (e.g., "100G")
	OverlayLowerPath     string   // Path to lower directory (read-only base layer) - deprecated
	OverlayLowerPaths    []string // Paths to lower directories (read-only base layers)
	OverlayTargetPath    string   // Where to mount the final overlay
	OverlaySkipOverlayFS bool     // Skip overlayfs, only mount loopback

	// Proxy configuration
	ProxyLocalhostIPv4 string // IPv4 address to use when proxying to localhost
	ProxyLocalhostIPv6 string // IPv6 address to use when proxying to localhost

	// Admin channel
	AdminChannelURL string // Override default admin channel URL

	// Health monitoring
	HealthCheckInterval time.Duration // How often to check system health

	// Derived fields
	WriteDir        string // SPRITE_WRITE_DIR
	LogDir          string // WriteDir/logs
	JuiceFSDataPath string // JuiceFSBaseDir or WriteDir/juicefs
}

// GetOverlayLowerPaths returns the overlay lower paths with priority and fallback logic
func (c *Config) GetOverlayLowerPaths() []string {
	// Prioritize array format
	if len(c.OverlayLowerPaths) > 0 {
		return c.OverlayLowerPaths
	}

	// Fall back to single string format
	if c.OverlayLowerPath != "" {
		return []string{c.OverlayLowerPath}
	}

	// Default fallback
	return []string{"/mnt/system-base"}
}

// Validate checks if the configuration is valid
func (c *Config) Validate() error {
	// WriteDir is required
	if c.WriteDir == "" {
		return fmt.Errorf("SPRITE_WRITE_DIR environment variable is not set")
	}

	// API token is required if API server is enabled
	if c.APIListenAddr != "" && c.APIToken == "" {
		return fmt.Errorf("API token must be set when API server is enabled")
	}

	// S3 configuration validation
	hasS3 := c.S3AccessKey != "" || c.S3SecretAccessKey != "" || c.S3EndpointURL != "" || c.S3Bucket != ""
	if hasS3 {
		// If any S3 config is provided, all must be provided
		if c.S3AccessKey == "" || c.S3SecretAccessKey == "" || c.S3EndpointURL == "" || c.S3Bucket == "" {
			return fmt.Errorf("incomplete S3 configuration: all of S3_ACCESS_KEY, S3_SECRET_ACCESS_KEY, S3_ENDPOINT_URL, and S3_BUCKET must be set")
		}
	}

	return nil
}

// ParseConfig parses configuration from command line flags and environment variables
func ParseConfig() (*Config, error) {
	config := &Config{}

	// Define command line flags
	var (
		configFile              string
		debug                   bool
		logJSON                 bool
		listenAddr              string
		gracefulShutdownTimeout time.Duration
		juicefsDirFlag          string
		showVersion             bool
	)

	flag.StringVar(&configFile, "config", "", "JSON configuration file")
	flag.BoolVar(&debug, "debug", false, "Enable debug logging")
	flag.BoolVar(&logJSON, "log-json", false, "Output logs in JSON format")
	flag.StringVar(&listenAddr, "listen", "", "API server listen address")
	flag.DurationVar(&gracefulShutdownTimeout, "graceful-shutdown-timeout", 30*time.Second, "Process graceful shutdown timeout")
	flag.StringVar(&juicefsDirFlag, "juicefs-dir", "", "JuiceFS base directory")
	flag.BoolVar(&showVersion, "version", false, "Show version and exit")
	flag.Parse()

	if showVersion {
		fmt.Printf("sprite-env version %s\n", version)
		os.Exit(0)
	}

	// Load from config file if specified
	if configFile != "" {
		if err := loadConfigFile(configFile, config); err != nil {
			return nil, err
		}
	}

	// Apply environment variables (override file config)
	applyEnvironmentVariables(config)

	// Apply command line flags (override everything)
	if debug {
		config.Debug = true
		config.LogLevel = slog.LevelDebug
	}
	if logJSON {
		config.LogJSON = true
	}
	if listenAddr != "" {
		config.APIListenAddr = listenAddr
	}
	if juicefsDirFlag != "" {
		config.JuiceFSBaseDir = juicefsDirFlag
	}
	config.ProcessGracefulShutdownTimeout = gracefulShutdownTimeout

	// Get process command from remaining args
	args := flag.Args()
	if len(args) > 0 {
		config.ProcessCommand = args
	}

	// Set derived fields
	config.WriteDir = os.Getenv("SPRITE_WRITE_DIR")
	if config.WriteDir != "" {
		config.LogDir = filepath.Join(config.WriteDir, "logs")
		if config.JuiceFSBaseDir == "" {
			config.JuiceFSDataPath = filepath.Join(config.WriteDir, "juicefs")
		} else {
			config.JuiceFSDataPath = config.JuiceFSBaseDir
		}
	}

	// Validate configuration
	if err := config.Validate(); err != nil {
		return nil, err
	}

	return config, nil
}

// loadConfigFile loads configuration from a JSON file
func loadConfigFile(filename string, config *Config) error {
	data, err := os.ReadFile(filename)
	if err != nil {
		return fmt.Errorf("failed to read config file: %w", err)
	}

	// Define the JSON structure
	var fileConfig struct {
		LogLevel           string   `json:"log_level"`
		LogJSON            bool     `json:"log_json"`
		APIListen          string   `json:"api_listen_addr"`
		ProcessCmd         []string `json:"process_command"`
		ProcessDir         string   `json:"process_working_dir"`
		ProcessEnv         []string `json:"process_environment"`
		ExecWrapperCommand []string `json:"exec_wrapper_command"`

		// JuiceFS configuration
		JuiceFSEnabled    bool   `json:"juicefs_enabled"`
		JuiceFSBaseDir    string `json:"juicefs_base_dir"`
		JuiceFSLocalMode  bool   `json:"juicefs_local_mode"`
		JuiceFSVolumeName string `json:"juicefs_volume_name"`
		S3AccessKey       string `json:"s3_access_key"`
		S3SecretAccessKey string `json:"s3_secret_access_key"`
		S3EndpointURL     string `json:"s3_endpoint_url"`
		S3Bucket          string `json:"s3_bucket"`

		// Overlay configuration
		OverlayEnabled       bool     `json:"overlay_enabled"`
		OverlayImageSize     string   `json:"overlay_image_size"`
		OverlayLowerPath     string   `json:"overlay_lower_path"`
		OverlayLowerPaths    []string `json:"overlay_lower_paths"`
		OverlayTargetPath    string   `json:"overlay_target_path"`
		OverlaySkipOverlayFS bool     `json:"overlay_skip_overlayfs"`

		// Proxy configuration
		ProxyLocalhostIPv4 string `json:"proxy_localhost_ipv4"`
		ProxyLocalhostIPv6 string `json:"proxy_localhost_ipv6"`
	}

	if err := json.Unmarshal(data, &fileConfig); err != nil {
		return fmt.Errorf("failed to parse config file: %w", err)
	}

	// Apply file config to main config
	if fileConfig.LogLevel != "" {
		switch strings.ToLower(fileConfig.LogLevel) {
		case "debug":
			config.LogLevel = slog.LevelDebug
		case "info":
			config.LogLevel = slog.LevelInfo
		case "warn", "warning":
			config.LogLevel = slog.LevelWarn
		case "error":
			config.LogLevel = slog.LevelError
		default:
			return fmt.Errorf("invalid log level in config file: %s", fileConfig.LogLevel)
		}
	}

	config.LogJSON = fileConfig.LogJSON
	config.APIListenAddr = fileConfig.APIListen
	config.ProcessCommand = fileConfig.ProcessCmd
	config.ProcessWorkingDir = fileConfig.ProcessDir
	config.ProcessEnvironment = fileConfig.ProcessEnv
	config.ExecWrapperCommand = fileConfig.ExecWrapperCommand

	config.JuiceFSBaseDir = fileConfig.JuiceFSBaseDir
	config.JuiceFSLocalMode = fileConfig.JuiceFSLocalMode
	config.S3AccessKey = fileConfig.S3AccessKey
	config.S3SecretAccessKey = fileConfig.S3SecretAccessKey
	config.S3EndpointURL = fileConfig.S3EndpointURL
	config.S3Bucket = fileConfig.S3Bucket

	config.OverlayEnabled = fileConfig.OverlayEnabled
	config.OverlayImageSize = fileConfig.OverlayImageSize
	config.OverlayLowerPath = fileConfig.OverlayLowerPath
	config.OverlayLowerPaths = fileConfig.OverlayLowerPaths
	config.OverlayTargetPath = fileConfig.OverlayTargetPath
	config.OverlaySkipOverlayFS = fileConfig.OverlaySkipOverlayFS

	config.ProxyLocalhostIPv4 = fileConfig.ProxyLocalhostIPv4
	config.ProxyLocalhostIPv6 = fileConfig.ProxyLocalhostIPv6

	return nil
}

// applyEnvironmentVariables applies environment variable overrides to the config
func applyEnvironmentVariables(config *Config) {
	// Logging
	if logLevel := os.Getenv("LOG_LEVEL"); logLevel != "" {
		switch strings.ToLower(logLevel) {
		case "debug":
			config.LogLevel = slog.LevelDebug
		case "info":
			config.LogLevel = slog.LevelInfo
		case "warn", "warning":
			config.LogLevel = slog.LevelWarn
		case "error":
			config.LogLevel = slog.LevelError
		}
	}

	// API configuration
	config.APIToken = os.Getenv("SPRITE_HTTP_API_TOKEN")
	config.AdminToken = os.Getenv("SPRITE_HTTP_ADMIN_TOKEN")
	config.AdminChannelURL = os.Getenv("SPRITE_ADMIN_CHANNEL")

	// S3 configuration
	if s3Key := os.Getenv("SPRITE_S3_ACCESS_KEY"); s3Key != "" {
		config.S3AccessKey = s3Key
	}
	if s3Secret := os.Getenv("SPRITE_S3_SECRET_ACCESS_KEY"); s3Secret != "" {
		config.S3SecretAccessKey = s3Secret
	}
	if s3Endpoint := os.Getenv("SPRITE_S3_ENDPOINT_URL"); s3Endpoint != "" {
		config.S3EndpointURL = s3Endpoint
	}
	if s3Bucket := os.Getenv("SPRITE_S3_BUCKET"); s3Bucket != "" {
		config.S3Bucket = s3Bucket
	}

	// Overlay configuration
	if overlayEnabled := os.Getenv("SPRITE_OVERLAY_ENABLED"); overlayEnabled == "true" {
		config.OverlayEnabled = true
	} else if overlayEnabled == "false" {
		config.OverlayEnabled = false
	}
	if overlaySize := os.Getenv("SPRITE_OVERLAY_IMAGE_SIZE"); overlaySize != "" {
		config.OverlayImageSize = overlaySize
	}
	if overlayLowerPath := os.Getenv("SPRITE_OVERLAY_LOWER_PATH"); overlayLowerPath != "" {
		config.OverlayLowerPath = overlayLowerPath
	}
	// New environment variable for multiple lower paths (colon-separated)
	if overlayLowerPaths := os.Getenv("SPRITE_OVERLAY_LOWER_PATHS"); overlayLowerPaths != "" {
		config.OverlayLowerPaths = strings.Split(overlayLowerPaths, ":")
	}
	if overlayTarget := os.Getenv("SPRITE_OVERLAY_TARGET_PATH"); overlayTarget != "" {
		config.OverlayTargetPath = overlayTarget
	}
	if skipOverlayFS := os.Getenv("SPRITE_OVERLAY_SKIP_OVERLAYFS"); skipOverlayFS == "true" {
		config.OverlaySkipOverlayFS = true
	} else if skipOverlayFS == "false" {
		config.OverlaySkipOverlayFS = false
	}

	// Proxy configuration
	if proxyIPv4 := os.Getenv("SPRITE_PROXY_LOCALHOST_IPV4"); proxyIPv4 != "" {
		config.ProxyLocalhostIPv4 = proxyIPv4
	}
	if proxyIPv6 := os.Getenv("SPRITE_PROXY_LOCALHOST_IPV6"); proxyIPv6 != "" {
		config.ProxyLocalhostIPv6 = proxyIPv6
	}

	// Debug configuration
	config.KeepAliveOnError = os.Getenv("SPRITE_KEEP_ALIVE_ON_ERROR") == "true"
	config.WaitForBoot = os.Getenv("WAIT_FOR_BOOT") == "true"
}
