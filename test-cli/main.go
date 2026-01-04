package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"log"
	"os"
	"strings"
	"time"

	sprites "github.com/superfly/sprites-go"
)

// LogEvent represents a structured log event
type LogEvent struct {
	Timestamp time.Time              `json:"timestamp"`
	Type      string                 `json:"type"`
	Data      map[string]interface{} `json:"data"`
}

// Logger handles writing structured log events
type Logger struct {
	file *os.File
}

func NewLogger(logPath string) (*Logger, error) {
	if logPath == "" {
		return &Logger{}, nil
	}

	file, err := os.OpenFile(logPath, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
	if err != nil {
		return nil, fmt.Errorf("failed to open log file: %w", err)
	}

	return &Logger{file: file}, nil
}

func (l *Logger) LogEvent(eventType string, data map[string]interface{}) {
	if l.file == nil {
		return
	}

	event := LogEvent{
		Timestamp: time.Now(),
		Type:      eventType,
		Data:      data,
	}

	jsonData, err := json.Marshal(event)
	if err != nil {
		log.Printf("Failed to marshal log event: %v", err)
		return
	}

	l.file.Write(jsonData)
	l.file.WriteString("\n")
	l.file.Sync()
}

func (l *Logger) Close() {
	if l.file != nil {
		l.file.Close()
	}
}

func main() {
	var (
		baseURL    = flag.String("base-url", "https://api.sprites.dev", "Base URL for the sprite API")
		spriteName = flag.String("sprite", "", "Sprite name to execute command on (required for exec commands)")
		dir        = flag.String("dir", "", "Working directory for the command")
		env        = flag.String("env", "", "Environment variables (comma-separated key=value pairs)")
		tty        = flag.Bool("tty", false, "Enable TTY mode")
		ttyRows    = flag.Int("tty-rows", 24, "TTY rows (height)")
		ttyCols    = flag.Int("tty-cols", 80, "TTY columns (width)")
		sessionID  = flag.String("session-id", "", "Attach to existing session ID")
		timeout    = flag.Duration("timeout", 0, "Command timeout (0 = no timeout)")
		output     = flag.String("output", "stdout", "Output mode: stdout, combined, exit-code")
		logTarget  = flag.String("log-target", "", "File path to write structured JSON logs")
		help       = flag.Bool("help", false, "Show help")
	)
	flag.Parse()

	if *help {
		showHelp()
		return
	}

	// Initialize logger
	logger, loggerErr := NewLogger(*logTarget)
	if loggerErr != nil {
		log.Fatalf("Error: failed to initialize logger: %v", loggerErr)
	}
	defer logger.Close()

	// Get token from environment variable
	token := os.Getenv("SPRITES_TOKEN")
	if token == "" {
		log.Fatal("Error: SPRITES_TOKEN environment variable is required")
	}

	// Get command and arguments
	args := flag.Args()
	if len(args) == 0 {
		log.Fatal("Error: command is required")
	}

	// Handle special commands that don't require a sprite
	command := args[0]
	switch command {
	case "create":
		if len(args) < 2 {
			log.Fatal("Error: sprite name is required for create command")
		}
		createSprite(token, *baseURL, args[1], logger)
		return
	case "destroy":
		if len(args) < 2 {
			log.Fatal("Error: sprite name is required for destroy command")
		}
		destroySprite(token, *baseURL, args[1], logger)
		return
	}

	// For exec commands, sprite name is required
	if *spriteName == "" {
		log.Fatal("Error: -sprite is required for exec commands")
	}

	// Log command start
	logger.LogEvent("command_start", map[string]interface{}{
		"sprite":     *spriteName,
		"command":    args[0],
		"args":       args[1:],
		"base_url":   *baseURL,
		"tty":        *tty,
		"session_id": *sessionID,
		"timeout":    timeout.String(),
		"output":     *output,
	})

	// Create client
	client := sprites.New(token, sprites.WithBaseURL(*baseURL))
	sprite := client.Sprite(*spriteName)

	// Create context with optional timeout
	ctx := context.Background()
	if *timeout > 0 {
		var cancel context.CancelFunc
		ctx, cancel = context.WithTimeout(ctx, *timeout)
		defer cancel()
	}

	// Create command
	var cmd *sprites.Cmd
	if *sessionID != "" {
		// Attach to existing session
		cmd = sprite.AttachSessionContext(ctx, *sessionID)
		logger.LogEvent("session_attach", map[string]interface{}{
			"session_id": *sessionID,
		})
	} else {
		// Regular command
		cmd = sprite.CommandContext(ctx, args[0], args[1:]...)
	}

	// Set up text message handler for all messages
	cmd.TextMessageHandler = func(data []byte) {
		// Try to parse as JSON for structured messages
		var msg map[string]interface{}
		if err := json.Unmarshal(data, &msg); err == nil {
			// Log structured messages
			if msgType, ok := msg["type"].(string); ok {
				logger.LogEvent("text_message", map[string]interface{}{
					"message_type": msgType,
					"data":         msg,
				})
			} else {
				logger.LogEvent("text_message", map[string]interface{}{
					"raw_data": string(data),
				})
			}
		} else {
			// Log raw text messages
			logger.LogEvent("text_message", map[string]interface{}{
				"raw_data": string(data),
			})
		}
	}

	// Set options
	if *dir != "" {
		cmd.Dir = *dir
	}

	if *env != "" {
		cmd.Env = strings.Split(*env, ",")
	}

	if *tty {
		cmd.SetTTY(true)
		if *ttyRows > 0 && *ttyCols > 0 {
			cmd.SetTTYSize(uint16(*ttyRows), uint16(*ttyCols))
		}
		logger.LogEvent("tty_configured", map[string]interface{}{
			"rows": *ttyRows,
			"cols": *ttyCols,
		})
	}

	// Execute command based on output mode
	var cmdErr error
	var exitCode int
	var outputData []byte

	switch *output {
	case "stdout":
		outputData, cmdErr = cmd.Output()
		if cmdErr != nil {
			if exitErr, ok := cmdErr.(*sprites.ExitError); ok {
				exitCode = exitErr.ExitCode()
			}
			logger.LogEvent("command_failed", map[string]interface{}{
				"error":     cmdErr.Error(),
				"exit_code": exitCode,
			})
			log.Fatalf("Command failed: %v", cmdErr)
		}
		fmt.Print(string(outputData))
		logger.LogEvent("command_completed", map[string]interface{}{
			"exit_code":     0,
			"output_length": len(outputData),
		})
	case "combined":
		outputData, cmdErr = cmd.CombinedOutput()
		if cmdErr != nil {
			if exitErr, ok := cmdErr.(*sprites.ExitError); ok {
				exitCode = exitErr.ExitCode()
			}
			logger.LogEvent("command_failed", map[string]interface{}{
				"error":     cmdErr.Error(),
				"exit_code": exitCode,
			})
			log.Fatalf("Command failed: %v", cmdErr)
		}
		fmt.Print(string(outputData))
		logger.LogEvent("command_completed", map[string]interface{}{
			"exit_code":     0,
			"output_length": len(outputData),
		})
	case "exit-code":
		cmdErr = cmd.Run()
		if cmdErr != nil {
			if exitErr, ok := cmdErr.(*sprites.ExitError); ok {
				exitCode = exitErr.ExitCode()
				logger.LogEvent("command_completed", map[string]interface{}{
					"exit_code": exitCode,
				})
				os.Exit(exitCode)
			}
			logger.LogEvent("command_failed", map[string]interface{}{
				"error": cmdErr.Error(),
			})
			log.Fatalf("Command failed: %v", cmdErr)
		}
		logger.LogEvent("command_completed", map[string]interface{}{
			"exit_code": 0,
		})
	default:
		// Default: run and show output
		cmd.Stdout = os.Stdout
		cmd.Stderr = os.Stderr
		cmd.Stdin = os.Stdin
		cmdErr = cmd.Run()
		if cmdErr != nil {
			if exitErr, ok := cmdErr.(*sprites.ExitError); ok {
				exitCode = exitErr.ExitCode()
				logger.LogEvent("command_completed", map[string]interface{}{
					"exit_code": exitCode,
				})
				os.Exit(exitCode)
			}
			logger.LogEvent("command_failed", map[string]interface{}{
				"error": cmdErr.Error(),
			})
			log.Fatalf("Command failed: %v", cmdErr)
		}
		logger.LogEvent("command_completed", map[string]interface{}{
			"exit_code": 0,
		})
	}
}

func createSprite(token, baseURL, spriteName string, logger *Logger) {
	logger.LogEvent("sprite_create_start", map[string]interface{}{
		"sprite_name": spriteName,
		"base_url":    baseURL,
	})

	// Create client
	client := sprites.New(token, sprites.WithBaseURL(baseURL))

	// Create sprite with default configuration
	ctx := context.Background()
	sprite, err := client.CreateSprite(ctx, spriteName, nil)
	if err != nil {
		logger.LogEvent("sprite_create_failed", map[string]interface{}{
			"sprite_name": spriteName,
			"error":       err.Error(),
		})
		log.Fatalf("Failed to create sprite: %v", err)
	}

	logger.LogEvent("sprite_create_completed", map[string]interface{}{
		"sprite_name": sprite.Name(),
	})

	fmt.Printf("✅ Sprite '%s' created successfully\n", sprite.Name())
}

func destroySprite(token, baseURL, spriteName string, logger *Logger) {
	logger.LogEvent("sprite_destroy_start", map[string]interface{}{
		"sprite_name": spriteName,
		"base_url":    baseURL,
	})

	// Create client
	client := sprites.New(token, sprites.WithBaseURL(baseURL))

	// Destroy sprite
	ctx := context.Background()
	err := client.DeleteSprite(ctx, spriteName)
	if err != nil {
		logger.LogEvent("sprite_destroy_failed", map[string]interface{}{
			"sprite_name": spriteName,
			"error":       err.Error(),
		})
		log.Fatalf("Failed to destroy sprite: %v", err)
	}

	logger.LogEvent("sprite_destroy_completed", map[string]interface{}{
		"sprite_name": spriteName,
	})

	fmt.Printf("✅ Sprite '%s' destroyed successfully\n", spriteName)
}

func showHelp() {
	fmt.Println("Sprite SDK CLI")
	fmt.Println("==============")
	fmt.Println()
	fmt.Println("A command-line interface for executing commands on sprites using the Sprite SDK.")
	fmt.Println("This tool allows you to test various exec functionality with different options.")
	fmt.Println()
	fmt.Println("Usage:")
	fmt.Println("  test-cli [options] <command> [args...]")
	fmt.Println("  test-cli create <sprite-name>")
	fmt.Println("  test-cli destroy <sprite-name>")
	fmt.Println()
	fmt.Println("Required:")
	fmt.Println("  SPRITES_TOKEN environment variable")
	fmt.Println("        Authentication token (required)")
	fmt.Println("  -sprite string")
	fmt.Println("        Sprite name to execute command on (required for exec commands)")
	fmt.Println()
	fmt.Println("Optional Options:")
	fmt.Println("  -base-url string")
	fmt.Println("        Base URL for the sprite API (default: https://api.sprites.dev)")
	fmt.Println("  -dir string")
	fmt.Println("        Working directory for the command")
	fmt.Println("  -env string")
	fmt.Println("        Environment variables (comma-separated key=value pairs)")
	fmt.Println("  -tty")
	fmt.Println("        Enable TTY mode")
	fmt.Println("  -tty-rows int")
	fmt.Println("        TTY rows/height (default: 24)")
	fmt.Println("  -tty-cols int")
	fmt.Println("        TTY columns/width (default: 80)")
	fmt.Println("  -session-id string")
	fmt.Println("        Attach to existing session ID")
	fmt.Println("  -timeout duration")
	fmt.Println("        Command timeout (0 = no timeout)")
	fmt.Println("  -output string")
	fmt.Println("        Output mode: stdout, combined, exit-code (default: stdout)")
	fmt.Println("  -log-target string")
	fmt.Println("        File path to write structured JSON logs")
	fmt.Println("  -help")
	fmt.Println("        Show this help message")
	fmt.Println()
	fmt.Println("Output Modes:")
	fmt.Println("  stdout     - Capture and return stdout only")
	fmt.Println("  combined   - Capture and return combined stdout/stderr")
	fmt.Println("  exit-code  - Run command and exit with its exit code")
	fmt.Println("  (default)  - Stream output directly to terminal")
	fmt.Println()
	fmt.Println("Structured Logging:")
	fmt.Println("  When -log-target is specified, the CLI writes JSON events to the file:")
	fmt.Println("  - command_start/completed/failed - Command lifecycle events")
	fmt.Println("  - session_attach - Session attachment events")
	fmt.Println("  - tty_configured - TTY configuration events")
	fmt.Println("  - port_opened/port_closed - Port events with typed data")
	fmt.Println("  - text_message - Other server messages")
	fmt.Println()
	fmt.Println("Examples:")
	fmt.Println("  # Create a sprite")
	fmt.Println("  SPRITES_TOKEN=mytoken test-cli create my-test-sprite")
	fmt.Println()
	fmt.Println("  # Destroy a sprite")
	fmt.Println("  SPRITES_TOKEN=mytoken test-cli destroy my-test-sprite")
	fmt.Println()
	fmt.Println("  # Basic command execution")
	fmt.Println("  SPRITES_TOKEN=mytoken test-cli -sprite mysprite echo 'hello world'")
	fmt.Println()
	fmt.Println("  # Command with environment variables")
	fmt.Println("  SPRITES_TOKEN=mytoken test-cli -sprite mysprite -env 'FOO=bar,BAZ=qux' env")
	fmt.Println()
	fmt.Println("  # TTY command")
	fmt.Println("  SPRITES_TOKEN=mytoken test-cli -sprite mysprite -tty -tty-rows 30 -tty-cols 100 bash")
	fmt.Println()
	fmt.Println("  # Attach to existing session")
	fmt.Println("  SPRITES_TOKEN=mytoken test-cli -sprite mysprite -session-id session123")
	fmt.Println()
	fmt.Println("  # Command with timeout")
	fmt.Println("  SPRITES_TOKEN=mytoken test-cli -sprite mysprite -timeout 10s sleep 5")
	fmt.Println()
	fmt.Println("  # Capture output")
	fmt.Println("  SPRITES_TOKEN=mytoken test-cli -sprite mysprite -output stdout ls -la")
	fmt.Println()
	fmt.Println("  # With structured logging (includes port events)")
	fmt.Println("  SPRITES_TOKEN=mytoken test-cli -sprite mysprite -log-target /tmp/sprite.log echo 'hello'")
}
