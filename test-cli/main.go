package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"log"
	"os"
	"strconv"
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

		// Filesystem flags
		fsPath      = flag.String("path", "", "Path for filesystem operations")
		fsContent   = flag.String("content", "", "Content for fs-write")
		fsParents   = flag.Bool("parents", false, "Create parent directories for fs-mkdir")
		fsRecursive = flag.Bool("recursive", false, "Recursive operation for fs-rm")
		fsOld       = flag.String("old", "", "Old path for fs-rename")
		fsNew       = flag.String("new", "", "New path for fs-rename")
		fsSrc       = flag.String("src", "", "Source path for fs-copy")
		fsDst       = flag.String("dst", "", "Destination path for fs-copy")
		fsMode      = flag.String("mode", "", "File mode for fs-chmod (e.g., 0755)")
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
	case "policy":
		if *spriteName == "" {
			log.Fatal("Error: -sprite is required for policy command")
		}
		handlePolicyCommand(token, *baseURL, *spriteName, args[1:], logger)
		return
	case "checkpoint":
		if *spriteName == "" {
			log.Fatal("Error: -sprite is required for checkpoint command")
		}
		handleCheckpointCommand(token, *baseURL, *spriteName, args[1:], logger)
		return
	case "fs-write":
		if *spriteName == "" {
			log.Fatal("Error: -sprite is required for fs-write command")
		}
		if *fsPath == "" {
			log.Fatal("Error: -path is required for fs-write command")
		}
		handleFsWrite(token, *baseURL, *spriteName, *dir, *fsPath, *fsContent, logger)
		return
	case "fs-read":
		if *spriteName == "" {
			log.Fatal("Error: -sprite is required for fs-read command")
		}
		if *fsPath == "" {
			log.Fatal("Error: -path is required for fs-read command")
		}
		handleFsRead(token, *baseURL, *spriteName, *dir, *fsPath, logger)
		return
	case "fs-list":
		if *spriteName == "" {
			log.Fatal("Error: -sprite is required for fs-list command")
		}
		if *fsPath == "" {
			log.Fatal("Error: -path is required for fs-list command")
		}
		handleFsList(token, *baseURL, *spriteName, *dir, *fsPath, logger)
		return
	case "fs-stat":
		if *spriteName == "" {
			log.Fatal("Error: -sprite is required for fs-stat command")
		}
		if *fsPath == "" {
			log.Fatal("Error: -path is required for fs-stat command")
		}
		handleFsStat(token, *baseURL, *spriteName, *dir, *fsPath, logger)
		return
	case "fs-mkdir":
		if *spriteName == "" {
			log.Fatal("Error: -sprite is required for fs-mkdir command")
		}
		if *fsPath == "" {
			log.Fatal("Error: -path is required for fs-mkdir command")
		}
		handleFsMkdir(token, *baseURL, *spriteName, *dir, *fsPath, *fsParents, logger)
		return
	case "fs-rm":
		if *spriteName == "" {
			log.Fatal("Error: -sprite is required for fs-rm command")
		}
		if *fsPath == "" {
			log.Fatal("Error: -path is required for fs-rm command")
		}
		handleFsRm(token, *baseURL, *spriteName, *dir, *fsPath, *fsRecursive, logger)
		return
	case "fs-rename":
		if *spriteName == "" {
			log.Fatal("Error: -sprite is required for fs-rename command")
		}
		if *fsOld == "" || *fsNew == "" {
			log.Fatal("Error: -old and -new are required for fs-rename command")
		}
		handleFsRename(token, *baseURL, *spriteName, *dir, *fsOld, *fsNew, logger)
		return
	case "fs-copy":
		if *spriteName == "" {
			log.Fatal("Error: -sprite is required for fs-copy command")
		}
		if *fsSrc == "" || *fsDst == "" {
			log.Fatal("Error: -src and -dst are required for fs-copy command")
		}
		handleFsCopy(token, *baseURL, *spriteName, *dir, *fsSrc, *fsDst, logger)
		return
	case "fs-chmod":
		if *spriteName == "" {
			log.Fatal("Error: -sprite is required for fs-chmod command")
		}
		if *fsPath == "" || *fsMode == "" {
			log.Fatal("Error: -path and -mode are required for fs-chmod command")
		}
		handleFsChmod(token, *baseURL, *spriteName, *dir, *fsPath, *fsMode, logger)
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

func handlePolicyCommand(token, baseURL, spriteName string, args []string, logger *Logger) {
	if len(args) == 0 {
		log.Fatal("Error: policy subcommand required (get, set)")
	}

	client := sprites.New(token, sprites.WithBaseURL(baseURL))
	sprite := client.Sprite(spriteName)
	ctx := context.Background()

	subcommand := args[0]
	switch subcommand {
	case "get":
		logger.LogEvent("policy_get_start", map[string]interface{}{
			"sprite": spriteName,
		})
		policy, err := sprite.GetNetworkPolicy(ctx)
		if err != nil {
			logger.LogEvent("policy_get_failed", map[string]interface{}{
				"error": err.Error(),
			})
			log.Fatalf("Failed to get network policy: %v", err)
		}
		logger.LogEvent("policy_get_completed", map[string]interface{}{
			"rules_count": len(policy.Rules),
		})
		output, _ := json.MarshalIndent(policy, "", "  ")
		fmt.Println(string(output))

	case "set":
		if len(args) < 2 {
			log.Fatal("Error: policy JSON required (policy set '<json>')")
		}
		policyJSON := args[1]
		var policy sprites.NetworkPolicy
		if err := json.Unmarshal([]byte(policyJSON), &policy); err != nil {
			log.Fatalf("Invalid policy JSON: %v", err)
		}
		logger.LogEvent("policy_set_start", map[string]interface{}{
			"sprite":      spriteName,
			"rules_count": len(policy.Rules),
		})
		err := sprite.UpdateNetworkPolicy(ctx, &policy)
		if err != nil {
			logger.LogEvent("policy_set_failed", map[string]interface{}{
				"error": err.Error(),
			})
			log.Fatalf("Failed to set network policy: %v", err)
		}
		logger.LogEvent("policy_set_completed", map[string]interface{}{
			"rules_count": len(policy.Rules),
		})
		fmt.Println("Network policy updated")

	default:
		log.Fatalf("Unknown policy subcommand: %s", subcommand)
	}
}

func handleCheckpointCommand(token, baseURL, spriteName string, args []string, logger *Logger) {
	if len(args) == 0 {
		log.Fatal("Error: checkpoint subcommand required (list, create, get, restore)")
	}

	client := sprites.New(token, sprites.WithBaseURL(baseURL))
	sprite := client.Sprite(spriteName)
	ctx := context.Background()

	subcommand := args[0]
	switch subcommand {
	case "list":
		logger.LogEvent("checkpoint_list_start", map[string]interface{}{
			"sprite": spriteName,
		})
		checkpoints, err := sprite.ListCheckpoints(ctx, "")
		if err != nil {
			logger.LogEvent("checkpoint_list_failed", map[string]interface{}{
				"error": err.Error(),
			})
			log.Fatalf("Failed to list checkpoints: %v", err)
		}
		logger.LogEvent("checkpoint_list_completed", map[string]interface{}{
			"count": len(checkpoints),
		})
		output, _ := json.MarshalIndent(checkpoints, "", "  ")
		fmt.Println(string(output))

	case "create":
		comment := ""
		if len(args) >= 2 {
			comment = args[1]
		}
		logger.LogEvent("checkpoint_create_start", map[string]interface{}{
			"sprite":  spriteName,
			"comment": comment,
		})
		stream, err := sprite.CreateCheckpointWithComment(ctx, comment)
		if err != nil {
			logger.LogEvent("checkpoint_create_failed", map[string]interface{}{
				"error": err.Error(),
			})
			log.Fatalf("Failed to create checkpoint: %v", err)
		}
		err = stream.ProcessAll(func(msg *sprites.StreamMessage) error {
			output, _ := json.Marshal(msg)
			fmt.Println(string(output))
			return nil
		})
		if err != nil {
			log.Fatalf("Error processing stream: %v", err)
		}
		logger.LogEvent("checkpoint_create_completed", map[string]interface{}{
			"sprite": spriteName,
		})

	case "get":
		if len(args) < 2 {
			log.Fatal("Error: checkpoint ID required")
		}
		checkpointID := args[1]
		logger.LogEvent("checkpoint_get_start", map[string]interface{}{
			"sprite":     spriteName,
			"checkpoint": checkpointID,
		})
		checkpoint, err := sprite.GetCheckpoint(ctx, checkpointID)
		if err != nil {
			logger.LogEvent("checkpoint_get_failed", map[string]interface{}{
				"error": err.Error(),
			})
			log.Fatalf("Failed to get checkpoint: %v", err)
		}
		logger.LogEvent("checkpoint_get_completed", map[string]interface{}{
			"checkpoint": checkpointID,
		})
		output, _ := json.MarshalIndent(checkpoint, "", "  ")
		fmt.Println(string(output))

	case "restore":
		if len(args) < 2 {
			log.Fatal("Error: checkpoint ID required")
		}
		checkpointID := args[1]
		logger.LogEvent("checkpoint_restore_start", map[string]interface{}{
			"sprite":     spriteName,
			"checkpoint": checkpointID,
		})
		stream, err := sprite.RestoreCheckpoint(ctx, checkpointID)
		if err != nil {
			logger.LogEvent("checkpoint_restore_failed", map[string]interface{}{
				"error": err.Error(),
			})
			log.Fatalf("Failed to restore checkpoint: %v", err)
		}
		err = stream.ProcessAll(func(msg *sprites.StreamMessage) error {
			output, _ := json.Marshal(msg)
			fmt.Println(string(output))
			return nil
		})
		if err != nil {
			log.Fatalf("Error processing stream: %v", err)
		}
		logger.LogEvent("checkpoint_restore_completed", map[string]interface{}{
			"sprite":     spriteName,
			"checkpoint": checkpointID,
		})

	default:
		log.Fatalf("Unknown checkpoint subcommand: %s", subcommand)
	}
}

// Filesystem command handlers

func handleFsWrite(token, baseURL, spriteName, workingDir, path, content string, logger *Logger) {
	logger.LogEvent("fs_write_start", map[string]interface{}{
		"sprite": spriteName,
		"path":   path,
	})

	client := sprites.New(token, sprites.WithBaseURL(baseURL))
	sprite := client.Sprite(spriteName)

	var fsys sprites.FS
	if workingDir != "" {
		fsys = sprite.FilesystemAt(workingDir)
	} else {
		fsys = sprite.Filesystem()
	}

	err := fsys.WriteFile(path, []byte(content), 0644)
	if err != nil {
		logger.LogEvent("fs_write_failed", map[string]interface{}{
			"error": err.Error(),
		})
		log.Fatalf("Failed to write file: %v", err)
	}

	logger.LogEvent("fs_write_completed", map[string]interface{}{
		"path": path,
		"size": len(content),
	})
	fmt.Printf("Wrote %d bytes to %s\n", len(content), path)
}

func handleFsRead(token, baseURL, spriteName, workingDir, path string, logger *Logger) {
	logger.LogEvent("fs_read_start", map[string]interface{}{
		"sprite": spriteName,
		"path":   path,
	})

	client := sprites.New(token, sprites.WithBaseURL(baseURL))
	sprite := client.Sprite(spriteName)

	var fsys sprites.FS
	if workingDir != "" {
		fsys = sprite.FilesystemAt(workingDir)
	} else {
		fsys = sprite.Filesystem()
	}

	data, err := fsys.ReadFile(path)
	if err != nil {
		logger.LogEvent("fs_read_failed", map[string]interface{}{
			"error": err.Error(),
		})
		log.Fatalf("Failed to read file: %v", err)
	}

	logger.LogEvent("fs_read_completed", map[string]interface{}{
		"path": path,
		"size": len(data),
	})
	fmt.Print(string(data))
}

func handleFsList(token, baseURL, spriteName, workingDir, path string, logger *Logger) {
	logger.LogEvent("fs_list_start", map[string]interface{}{
		"sprite": spriteName,
		"path":   path,
	})

	client := sprites.New(token, sprites.WithBaseURL(baseURL))
	sprite := client.Sprite(spriteName)

	var fsys sprites.FS
	if workingDir != "" {
		fsys = sprite.FilesystemAt(workingDir)
	} else {
		fsys = sprite.Filesystem()
	}

	entries, err := fsys.ReadDir(path)
	if err != nil {
		logger.LogEvent("fs_list_failed", map[string]interface{}{
			"error": err.Error(),
		})
		log.Fatalf("Failed to list directory: %v", err)
	}

	// Build JSON output
	type entryInfo struct {
		Name  string `json:"name"`
		IsDir bool   `json:"isDir"`
		Mode  string `json:"mode"`
		Size  int64  `json:"size,omitempty"`
	}
	var result []entryInfo
	for _, e := range entries {
		info, _ := e.Info()
		entry := entryInfo{
			Name:  e.Name(),
			IsDir: e.IsDir(),
			Mode:  fmt.Sprintf("%04o", info.Mode().Perm()),
		}
		if !e.IsDir() {
			entry.Size = info.Size()
		}
		result = append(result, entry)
	}

	logger.LogEvent("fs_list_completed", map[string]interface{}{
		"path":  path,
		"count": len(entries),
	})

	output, _ := json.MarshalIndent(result, "", "  ")
	fmt.Println(string(output))
}

func handleFsStat(token, baseURL, spriteName, workingDir, path string, logger *Logger) {
	logger.LogEvent("fs_stat_start", map[string]interface{}{
		"sprite": spriteName,
		"path":   path,
	})

	client := sprites.New(token, sprites.WithBaseURL(baseURL))
	sprite := client.Sprite(spriteName)

	var fsys sprites.FS
	if workingDir != "" {
		fsys = sprite.FilesystemAt(workingDir)
	} else {
		fsys = sprite.Filesystem()
	}

	info, err := fsys.Stat(path)
	if err != nil {
		logger.LogEvent("fs_stat_failed", map[string]interface{}{
			"error": err.Error(),
		})
		log.Fatalf("Failed to stat file: %v", err)
	}

	result := map[string]interface{}{
		"name":    info.Name(),
		"size":    info.Size(),
		"mode":    fmt.Sprintf("%04o", info.Mode().Perm()),
		"isDir":   info.IsDir(),
		"modTime": info.ModTime().Format(time.RFC3339),
	}

	logger.LogEvent("fs_stat_completed", map[string]interface{}{
		"path": path,
	})

	output, _ := json.MarshalIndent(result, "", "  ")
	fmt.Println(string(output))
}

func handleFsMkdir(token, baseURL, spriteName, workingDir, path string, parents bool, logger *Logger) {
	logger.LogEvent("fs_mkdir_start", map[string]interface{}{
		"sprite":  spriteName,
		"path":    path,
		"parents": parents,
	})

	client := sprites.New(token, sprites.WithBaseURL(baseURL))
	sprite := client.Sprite(spriteName)

	var fsys sprites.FS
	if workingDir != "" {
		fsys = sprite.FilesystemAt(workingDir)
	} else {
		fsys = sprite.Filesystem()
	}

	var err error
	if parents {
		err = fsys.MkdirAll(path, 0755)
	} else {
		err = fsys.Mkdir(path, 0755)
	}
	if err != nil {
		logger.LogEvent("fs_mkdir_failed", map[string]interface{}{
			"error": err.Error(),
		})
		log.Fatalf("Failed to create directory: %v", err)
	}

	logger.LogEvent("fs_mkdir_completed", map[string]interface{}{
		"path": path,
	})
	fmt.Printf("Created directory: %s\n", path)
}

func handleFsRm(token, baseURL, spriteName, workingDir, path string, recursive bool, logger *Logger) {
	logger.LogEvent("fs_rm_start", map[string]interface{}{
		"sprite":    spriteName,
		"path":      path,
		"recursive": recursive,
	})

	client := sprites.New(token, sprites.WithBaseURL(baseURL))
	sprite := client.Sprite(spriteName)

	var fsys sprites.FS
	if workingDir != "" {
		fsys = sprite.FilesystemAt(workingDir)
	} else {
		fsys = sprite.Filesystem()
	}

	var err error
	if recursive {
		err = fsys.RemoveAll(path)
	} else {
		err = fsys.Remove(path)
	}
	if err != nil {
		logger.LogEvent("fs_rm_failed", map[string]interface{}{
			"error": err.Error(),
		})
		log.Fatalf("Failed to remove: %v", err)
	}

	logger.LogEvent("fs_rm_completed", map[string]interface{}{
		"path": path,
	})
	fmt.Printf("Removed: %s\n", path)
}

func handleFsRename(token, baseURL, spriteName, workingDir, oldPath, newPath string, logger *Logger) {
	logger.LogEvent("fs_rename_start", map[string]interface{}{
		"sprite":  spriteName,
		"oldPath": oldPath,
		"newPath": newPath,
	})

	client := sprites.New(token, sprites.WithBaseURL(baseURL))
	sprite := client.Sprite(spriteName)

	var fsys sprites.FS
	if workingDir != "" {
		fsys = sprite.FilesystemAt(workingDir)
	} else {
		fsys = sprite.Filesystem()
	}

	err := fsys.Rename(oldPath, newPath)
	if err != nil {
		logger.LogEvent("fs_rename_failed", map[string]interface{}{
			"error": err.Error(),
		})
		log.Fatalf("Failed to rename: %v", err)
	}

	logger.LogEvent("fs_rename_completed", map[string]interface{}{
		"oldPath": oldPath,
		"newPath": newPath,
	})
	fmt.Printf("Renamed %s -> %s\n", oldPath, newPath)
}

func handleFsCopy(token, baseURL, spriteName, workingDir, src, dst string, logger *Logger) {
	logger.LogEvent("fs_copy_start", map[string]interface{}{
		"sprite": spriteName,
		"src":    src,
		"dst":    dst,
	})

	client := sprites.New(token, sprites.WithBaseURL(baseURL))
	sprite := client.Sprite(spriteName)

	var fsys sprites.FS
	if workingDir != "" {
		fsys = sprite.FilesystemAt(workingDir)
	} else {
		fsys = sprite.Filesystem()
	}

	err := fsys.Copy(src, dst)
	if err != nil {
		logger.LogEvent("fs_copy_failed", map[string]interface{}{
			"error": err.Error(),
		})
		log.Fatalf("Failed to copy: %v", err)
	}

	logger.LogEvent("fs_copy_completed", map[string]interface{}{
		"src": src,
		"dst": dst,
	})
	fmt.Printf("Copied %s -> %s\n", src, dst)
}

func handleFsChmod(token, baseURL, spriteName, workingDir, path, modeStr string, logger *Logger) {
	logger.LogEvent("fs_chmod_start", map[string]interface{}{
		"sprite": spriteName,
		"path":   path,
		"mode":   modeStr,
	})

	client := sprites.New(token, sprites.WithBaseURL(baseURL))
	sprite := client.Sprite(spriteName)

	var fsys sprites.FS
	if workingDir != "" {
		fsys = sprite.FilesystemAt(workingDir)
	} else {
		fsys = sprite.Filesystem()
	}

	// Parse mode string (e.g., "0755" or "755")
	mode, err := parseOctalMode(modeStr)
	if err != nil {
		log.Fatalf("Invalid mode: %v", err)
	}

	err = fsys.Chmod(path, mode)
	if err != nil {
		logger.LogEvent("fs_chmod_failed", map[string]interface{}{
			"error": err.Error(),
		})
		log.Fatalf("Failed to chmod: %v", err)
	}

	logger.LogEvent("fs_chmod_completed", map[string]interface{}{
		"path": path,
		"mode": modeStr,
	})
	fmt.Printf("Changed mode of %s to %s\n", path, modeStr)
}

func parseOctalMode(s string) (os.FileMode, error) {
	// Handle both "755" and "0755" formats
	s = strings.TrimPrefix(s, "0")
	if s == "" {
		s = "0"
	}
	mode, err := strconv.ParseUint(s, 8, 32)
	if err != nil {
		return 0, fmt.Errorf("invalid octal mode: %s", s)
	}
	return os.FileMode(mode), nil
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
	fmt.Println("  test-cli -sprite <name> policy <subcommand> [args...]")
	fmt.Println("  test-cli -sprite <name> checkpoint <subcommand> [args...]")
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
	fmt.Println()
	fmt.Println("Services Commands:")
	fmt.Println("  services list                         - List all services")
	fmt.Println("  services get <name>                   - Get service details")
	fmt.Println("  services create <name> <cmd> [args]   - Create and start a service")
	fmt.Println("  services delete <name>                - Delete a service")
	fmt.Println("  services start <name>                 - Start a stopped service")
	fmt.Println("  services stop <name>                  - Stop a running service")
	fmt.Println("  services signal <name> <signal>       - Send signal to service")
	fmt.Println()
	fmt.Println("Policy Commands:")
	fmt.Println("  policy get                            - Get current network policy")
	fmt.Println("  policy set '<json>'                   - Set network policy")
	fmt.Println()
	fmt.Println("Checkpoint Commands:")
	fmt.Println("  checkpoint list                       - List all checkpoints")
	fmt.Println("  checkpoint create [comment]           - Create a checkpoint")
	fmt.Println("  checkpoint get <id>                   - Get checkpoint details")
	fmt.Println("  checkpoint restore <id>               - Restore to a checkpoint")
	fmt.Println()
	fmt.Println("Filesystem Commands:")
	fmt.Println("  fs-write -path <path> -content <text> - Write content to file")
	fmt.Println("  fs-read -path <path>                  - Read file to stdout")
	fmt.Println("  fs-list -path <path>                  - List directory (JSON output)")
	fmt.Println("  fs-stat -path <path>                  - Get file info (JSON output)")
	fmt.Println("  fs-mkdir -path <path> [-parents]      - Create directory")
	fmt.Println("  fs-rm -path <path> [-recursive]       - Remove file/directory")
	fmt.Println("  fs-rename -old <path> -new <path>     - Rename/move file")
	fmt.Println("  fs-copy -src <path> -dst <path>       - Copy file/directory")
	fmt.Println("  fs-chmod -path <path> -mode <mode>    - Change permissions (e.g., 0755)")
	fmt.Println()
	fmt.Println("Filesystem Examples:")
	fmt.Println("  # Write a file")
	fmt.Println("  test-cli -sprite mysprite fs-write -path /tmp/test.txt -content 'Hello World'")
	fmt.Println()
	fmt.Println("  # Read a file")
	fmt.Println("  test-cli -sprite mysprite fs-read -path /tmp/test.txt")
	fmt.Println()
	fmt.Println("  # List directory")
	fmt.Println("  test-cli -sprite mysprite fs-list -path /home/sprite")
	fmt.Println()
	fmt.Println("  # Create nested directories")
	fmt.Println("  test-cli -sprite mysprite fs-mkdir -path /tmp/a/b/c -parents")
	fmt.Println()
	fmt.Println("  # Remove directory recursively")
	fmt.Println("  test-cli -sprite mysprite fs-rm -path /tmp/mydir -recursive")
	fmt.Println()
	fmt.Println("  # Copy a file")
	fmt.Println("  test-cli -sprite mysprite fs-copy -src /tmp/file.txt -dst /tmp/file_backup.txt")
	fmt.Println()
	fmt.Println("  # Change file permissions")
	fmt.Println("  test-cli -sprite mysprite fs-chmod -path /tmp/script.sh -mode 0755")
}
