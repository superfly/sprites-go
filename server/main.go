package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"log/slog"
	"net/http"
	"os"
	"os/signal"
	"path/filepath"
	"syscall"
	"time"

	"sprite-env/lib"
)

// Application holds the main application state
type Application struct {
	coordinator *lib.Coordinator
	ctx         *lib.AppContext
	server      *http.Server
}

// NewApplication creates a new application instance
func NewApplication(config ApplicationConfig) *Application {
	// Create application context with configuration
	appCtx := lib.NewAppContext(&lib.AppConfig{
		LogLevel: config.LogLevel,
		LogJSON:  config.LogJSON,
		TLATrace: config.TLATrace,
		Debug:    config.Debug,
	})

	// Create component configurations
	dbConfig := lib.ComponentConfig{
		Type:              lib.ComponentTypeDB,
		StartCommand:      config.DBStartCommand,
		ReadyCommand:      config.DBReadyCommand,
		CheckpointCommand: config.DBCheckpointCommand,
		RestoreCommand:    config.DBRestoreCommand,
	}

	fsConfig := lib.ComponentConfig{
		Type:              lib.ComponentTypeFS,
		StartCommand:      config.FSStartCommand,
		ReadyCommand:      config.FSReadyCommand,
		CheckpointCommand: config.FSCheckpointCommand,
		RestoreCommand:    config.FSRestoreCommand,
	}

	processConfig := lib.ProcessConfig{
		Command:           config.ProcessCommand,
		WorkingDir:        config.ProcessWorkingDir,
		Environment:       config.ProcessEnvironment,
		RestartMaxRetries: config.ProcessRestartMaxRetries,
		RestartBackoffMax: config.ProcessRestartBackoffMax,
	}

	coordinatorConfig := lib.CoordinatorConfig{
		DBConfig:      dbConfig,
		FSConfig:      fsConfig,
		ProcessConfig: processConfig,
	}

	// Create coordinator
	coordinator := lib.NewCoordinator(coordinatorConfig, appCtx)

	// Create HTTP server for monitoring
	server := &http.Server{
		Addr: ":8080",
	}

	return &Application{
		coordinator: coordinator,
		ctx:         appCtx,
		server:      server,
	}
}

// ApplicationConfig holds configuration for the application
type ApplicationConfig struct {
	// Logging configuration
	LogLevel slog.Level
	LogJSON  bool
	TLATrace bool
	Debug    bool

	// DB component configuration (nil if scripts don't exist)
	DBStartCommand      []string
	DBReadyCommand      []string
	DBCheckpointCommand []string
	DBRestoreCommand    []string

	// FS component configuration (nil if scripts don't exist)
	FSStartCommand      []string
	FSReadyCommand      []string
	FSCheckpointCommand []string
	FSRestoreCommand    []string

	// Process configuration
	ProcessCommand           []string
	ProcessWorkingDir        string
	ProcessEnvironment       []string
	ProcessRestartMaxRetries int
	ProcessRestartBackoffMax time.Duration
}

// Start starts the application
func (app *Application) Start(ctx context.Context) error {
	app.ctx.Info("Starting sprite-env application")

	// Set up HTTP endpoints for monitoring
	app.setupHTTPEndpoints()

	// Start HTTP server in background
	go func() {
		if err := app.server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			app.ctx.Error("HTTP server error", err)
		}
	}()

	// Start the coordinator
	if err := app.coordinator.Start(ctx); err != nil {
		app.ctx.Error("Failed to start coordinator", err)
		return err
	}

	app.ctx.Info("Application started successfully")
	return nil
}

// Stop stops the application gracefully
func (app *Application) Stop(ctx context.Context) error {
	app.ctx.Info("Stopping sprite-env application")

	// Stop coordinator
	if err := app.coordinator.Stop(ctx); err != nil {
		app.ctx.Error("Failed to stop coordinator", err)
		// Continue with other cleanup
	}

	// Stop HTTP server
	if err := app.server.Shutdown(ctx); err != nil {
		app.ctx.Error("Failed to shutdown HTTP server", err)
	}

	app.ctx.Info("Application stopped")
	return nil
}

// setupHTTPEndpoints configures HTTP endpoints for monitoring
func (app *Application) setupHTTPEndpoints() {
	mux := http.NewServeMux()

	// Current state endpoint
	mux.HandleFunc("/state", func(w http.ResponseWriter, r *http.Request) {
		state := app.coordinator.GetCurrentState()
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(state)
	})

	// Health check endpoint
	mux.HandleFunc("/health", func(w http.ResponseWriter, r *http.Request) {
		health := map[string]interface{}{
			"status":  "ok",
			"running": app.coordinator.IsRunning(),
		}
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(health)
	})

	app.server.Handler = mux
}

// parseCommandLineArgs parses command line arguments and returns configuration
func parseCommandLineArgs() (ApplicationConfig, error) {
	var testDir string
	var debug bool
	var tlaTrace bool
	var logJSON bool

	flag.StringVar(&testDir, "test-dir", "", "Directory containing test scripts")
	flag.BoolVar(&debug, "debug", false, "Enable debug logging")
	flag.BoolVar(&tlaTrace, "tla-trace", false, "Enable TLA+ state change tracing")
	flag.BoolVar(&logJSON, "log-json", false, "Output logs in JSON format")
	flag.Parse()

	// Get supervised process path from remaining arguments
	args := flag.Args()
	if len(args) == 0 {
		return ApplicationConfig{}, fmt.Errorf("supervised process command is required")
	}

	if testDir == "" {
		return ApplicationConfig{}, fmt.Errorf("test-dir is required")
	}

	// Determine log level
	logLevel := slog.LevelInfo
	if debug {
		logLevel = slog.LevelDebug
	}

	// Helper function to check and resolve script paths
	checkScript := func(componentType, scriptType, scriptPath string) []string {
		if absPath, err := filepath.Abs(scriptPath); err == nil {
			if _, err := os.Stat(absPath); err == nil {
				if debug {
					fmt.Printf("Found %s %s script: %s\n", componentType, scriptType, absPath)
				}
				return []string{absPath}
			} else if debug {
				fmt.Printf("%s %s script not found: %s\n", componentType, scriptType, absPath)
			}
		}
		return nil
	}

	// Infer DB component scripts from test directory
	dbStartCommand := checkScript("DB", "start", filepath.Join(testDir, "db", "start.sh"))
	dbReadyCommand := checkScript("DB", "ready", filepath.Join(testDir, "db", "ready.sh"))
	dbCheckpointCommand := checkScript("DB", "checkpoint", filepath.Join(testDir, "db", "checkpoint.sh"))
	dbRestoreCommand := checkScript("DB", "restore", filepath.Join(testDir, "db", "restore.sh"))

	// Infer FS component scripts from test directory
	fsStartCommand := checkScript("FS", "start", filepath.Join(testDir, "fs", "start.sh"))
	fsReadyCommand := checkScript("FS", "ready", filepath.Join(testDir, "fs", "ready.sh"))
	fsCheckpointCommand := checkScript("FS", "checkpoint", filepath.Join(testDir, "fs", "checkpoint.sh"))
	fsRestoreCommand := checkScript("FS", "restore", filepath.Join(testDir, "fs", "restore.sh"))

	// Validate that required start commands exist
	if len(dbStartCommand) == 0 {
		return ApplicationConfig{}, fmt.Errorf("DB start script is required but not found: %s", filepath.Join(testDir, "db", "start.sh"))
	}
	if len(fsStartCommand) == 0 {
		return ApplicationConfig{}, fmt.Errorf("FS start script is required but not found: %s", filepath.Join(testDir, "fs", "start.sh"))
	}

	// Build configuration
	config := ApplicationConfig{
		LogLevel: logLevel,
		LogJSON:  logJSON,
		TLATrace: tlaTrace,
		Debug:    debug,

		// DB component configuration (nil if scripts don't exist)
		DBStartCommand:      dbStartCommand,
		DBReadyCommand:      dbReadyCommand,
		DBCheckpointCommand: dbCheckpointCommand,
		DBRestoreCommand:    dbRestoreCommand,

		// FS component configuration (nil if scripts don't exist)
		FSStartCommand:      fsStartCommand,
		FSReadyCommand:      fsReadyCommand,
		FSCheckpointCommand: fsCheckpointCommand,
		FSRestoreCommand:    fsRestoreCommand,

		// Process configuration
		ProcessCommand:           args,
		ProcessWorkingDir:        "",
		ProcessEnvironment:       []string{},
		ProcessRestartMaxRetries: 3,
		ProcessRestartBackoffMax: 60 * time.Second,
	}

	return config, nil
}

func main() {
	// Parse command line arguments
	config, err := parseCommandLineArgs()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		fmt.Fprintf(os.Stderr, "Usage: %s -test-dir <dir> [options] -- <supervised-process-command>\n", os.Args[0])
		os.Exit(1)
	}

	// Create application
	app := NewApplication(config)

	// Set up signal handling
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()

	sigChan := make(chan os.Signal, 1)
	signal.Notify(sigChan, syscall.SIGTERM, syscall.SIGINT)

	// Start application
	if err := app.Start(ctx); err != nil {
		app.ctx.Error("Failed to start application", err)
		os.Exit(1)
	}

	// Wait for signal or context cancellation
	select {
	case sig := <-sigChan:
		app.ctx.Info("Received signal, shutting down", "signal", sig)
		cancel()

		// Graceful shutdown with timeout
		shutdownCtx, shutdownCancel := context.WithTimeout(context.Background(), 30*time.Second)
		defer shutdownCancel()

		if err := app.Stop(shutdownCtx); err != nil {
			app.ctx.Error("Error during shutdown", err)
			os.Exit(1)
		}

		// Set exit code based on signal
		if sig == syscall.SIGTERM {
			os.Exit(143) // 128 + 15
		} else if sig == syscall.SIGINT {
			os.Exit(130) // 128 + 2
		}

	case <-ctx.Done():
		app.ctx.Info("Context cancelled, shutting down")
	}

	app.ctx.Info("Application exited cleanly")
}
