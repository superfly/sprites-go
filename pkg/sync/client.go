package sync

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"

	"github.com/gorilla/websocket"
)

const (
	// DefaultUploadChannels is the default number of parallel upload channels
	DefaultUploadChannels = 4
	// DefaultChunkSize is the default chunk size for file uploads
	DefaultChunkSize = 64 * 1024 // 64KB
)

// ClientConfig holds configuration for the sync client
type ClientConfig struct {
	TargetPath         string
	Branch             string
	IncludeUncommitted bool
	UploadChannels     int
	ChunkSize          int
	ProgressCallback   func(Progress)
	Logger             *slog.Logger
}

// Client handles the client-side sync operations
type Client struct {
	config       ClientConfig
	gitRepoPath  string
	logger       *slog.Logger
	mainConn     *websocket.Conn
	sessionToken string
	serverURL    string
	token        string
}

// NewClient creates a new sync client
func NewClient(gitRepoPath string, config ClientConfig) *Client {
	if config.UploadChannels <= 0 {
		config.UploadChannels = DefaultUploadChannels
	}
	if config.ChunkSize <= 0 {
		config.ChunkSize = DefaultChunkSize
	}

	if config.Logger == nil {
		config.Logger = slog.Default()
	}

	return &Client{
		config:      config,
		gitRepoPath: gitRepoPath,
		logger:      config.Logger,
	}
}

// Sync performs the repository sync operation with parallel stages
func (c *Client) Sync(ctx context.Context, serverURL, token string) error {
	// Validate git repository
	if !c.isGitRepository() {
		return fmt.Errorf("path is not a git repository: %s", c.gitRepoPath)
	}

	c.logger.Info("Starting multi-connection sync", "repo", c.gitRepoPath, "target", c.config.TargetPath)

	// Store connection details for transfer connections
	c.serverURL = serverURL
	c.token = token

	// Connect to server
	conn, err := c.connect(serverURL, token)
	if err != nil {
		return fmt.Errorf("failed to connect to server: %w", err)
	}
	defer conn.Close()

	return c.sync(ctx, conn)
}

// connect establishes WebSocket connection to the server
func (c *Client) connect(serverURL, token string) (*websocket.Conn, error) {
	u, err := url.Parse(serverURL)
	if err != nil {
		return nil, err
	}

	// Convert to WebSocket URL
	switch u.Scheme {
	case "http":
		u.Scheme = "ws"
	case "https":
		u.Scheme = "wss"
	case "ws", "wss":
		// Already WebSocket
	default:
		return nil, fmt.Errorf("unsupported scheme: %s", u.Scheme)
	}

	// Add sync endpoint with target path
	u.Path = strings.TrimSuffix(u.Path, "/") + "/sync"
	u.RawQuery = "target=" + url.QueryEscape(c.config.TargetPath)

	// Create request headers
	headers := http.Header{}
	headers.Set("Authorization", "Bearer "+token)

	// Connect
	conn, _, err := websocket.DefaultDialer.Dial(u.String(), headers)
	if err != nil {
		return nil, err
	}

	return conn, nil
}

// sync executes the sync with parallel walk/negotiate/transfer stages
func (c *Client) sync(ctx context.Context, conn *websocket.Conn) error {
	c.mainConn = conn

	var (
		fileChan     = make(chan FileInfo, 100) // walk -> negotiate
		transferChan = make(chan FileInfo, 100) // negotiate -> transfer
		errorChan    = make(chan error, 3)      // all stages -> main
	)

	ctx, cancel := context.WithCancel(ctx)
	defer cancel()

	// WaitGroup to track all stages
	var wg sync.WaitGroup

	// Stage 1: Filesystem walk
	wg.Add(1)
	go func() {
		defer wg.Done()
		defer close(fileChan)
		if err := c.walkFilesystem(ctx, fileChan); err != nil {
			select {
			case errorChan <- fmt.Errorf("walk stage failed: %w", err):
			case <-ctx.Done():
			}
			cancel()
		}
	}()

	// Stage 2: Negotiate files and get session token
	wg.Add(1)
	go func() {
		defer wg.Done()
		defer close(transferChan)

		if err := c.negotiateFilesStreaming(ctx, conn, fileChan, transferChan); err != nil {
			select {
			case errorChan <- fmt.Errorf("negotiate stage failed: %w", err):
			case <-ctx.Done():
			}
			cancel()
			return
		}

		// Only after negotiation is done do we start waiting for the final completion message.
		wg.Add(1)
		go func() {
			defer wg.Done()
			if err := c.waitForCompletion(ctx); err != nil {
				select {
				case errorChan <- fmt.Errorf("completion wait failed: %w", err):
				case <-ctx.Done():
				}
				cancel()
			}
		}()
	}()

	// Stage 3: Transfer files (multiple workers with separate connections)
	for i := 0; i < c.config.UploadChannels; i++ {
		wg.Add(1)
		go func(workerID int) {
			defer wg.Done()
			if err := c.transferFilesWithOwnConnection(ctx, transferChan, workerID); err != nil {
				select {
				case errorChan <- fmt.Errorf("transfer stage (worker %d) failed: %w", workerID, err):
				case <-ctx.Done():
				}
				cancel()
			}
		}(i)
	}

	done := make(chan struct{})
	go func() {
		wg.Wait()
		close(done)
	}()

	select {
	case err := <-errorChan:
		cancel()
		wg.Wait()
		return err
	case <-done:
		c.logger.Info("Multi-connection sync completed successfully")
		return nil
	case <-ctx.Done():
		wg.Wait()
		return ctx.Err()
	}
}

// walkFilesystem walks the filesystem and sends files to the channel
func (c *Client) walkFilesystem(ctx context.Context, fileChan chan<- FileInfo) error {
	c.logger.Info("Starting filesystem walk")

	// Get files to walk
	files, err := c.getFilesToWalk()
	if err != nil {
		return fmt.Errorf("failed to get files to walk: %w", err)
	}

	// Send files to channel as we discover them
	for _, filePath := range files {
		select {
		case <-ctx.Done():
			return ctx.Err()
		default:
		}

		fullPath := filepath.Join(c.gitRepoPath, filePath)
		hash, err := calculateFileHash(fullPath)
		if err != nil {
			c.logger.Error("Failed to calculate hash", "file", filePath, "error", err)
			continue // Skip files we can't hash
		}

		info, err := os.Stat(fullPath)
		if err != nil {
			c.logger.Error("Failed to stat file", "file", filePath, "error", err)
			continue // Skip files we can't stat
		}

		fileInfo := FileInfo{
			Path: filePath,
			Hash: hash,
			Size: info.Size(),
		}

		select {
		case fileChan <- fileInfo:
			c.logger.Debug("Discovered file", "path", filePath, "size", info.Size())
		case <-ctx.Done():
			return ctx.Err()
		}
	}

	c.logger.Info("Filesystem walk completed")
	return nil
}

// uploadFile uploads a single file
func (c *Client) uploadFile(ctx context.Context, conn *websocket.Conn, file FileInfo, channelID int) error {
	filePath := filepath.Join(c.gitRepoPath, file.Path)

	// Send upload start
	uploadStart := UploadStart{
		ChannelID: channelID,
		Path:      file.Path,
		Hash:      file.Hash,
		Size:      file.Size,
	}

	msg, err := NewMessage(MsgTypeUploadStart, uploadStart)
	if err != nil {
		return err
	}

	if err := conn.WriteJSON(msg); err != nil {
		return err
	}

	// Open file
	f, err := os.Open(filePath)
	if err != nil {
		return err
	}
	defer f.Close()

	// Send file data in chunks
	buf := make([]byte, c.config.ChunkSize)
	var offset int64

	for {
		select {
		case <-ctx.Done():
			return ctx.Err()
		default:
		}

		n, err := f.Read(buf)
		if err != nil && err != io.EOF {
			return err
		}

		if n == 0 {
			break
		}

		fileData := FileData{
			ChannelID: channelID,
			Path:      file.Path,
			Data:      buf[:n],
			Offset:    offset,
			Final:     err == io.EOF,
		}

		msg, err := NewMessage(MsgTypeFileData, fileData)
		if err != nil {
			return err
		}

		if err := conn.WriteJSON(msg); err != nil {
			return err
		}

		offset += int64(n)

		if fileData.Final {
			break
		}
	}

	// Send upload done
	uploadDone := UploadDone{
		ChannelID: channelID,
		Path:      file.Path,
		Hash:      file.Hash,
		Size:      file.Size,
	}

	msg, err = NewMessage(MsgTypeUploadDone, uploadDone)
	if err != nil {
		return err
	}

	if err := conn.WriteJSON(msg); err != nil {
		return err
	}

	// Wait for server response (success or error)
	c.logger.Debug("Waiting for upload response", "file", file.Path, "channel", channelID)
	var responseMsg Message
	if err := conn.ReadJSON(&responseMsg); err != nil {
		return fmt.Errorf("failed to read upload response: %w", err)
	}
	c.logger.Debug("Received upload response", "file", file.Path, "type", responseMsg.Type)

	switch responseMsg.Type {
	case MsgTypeUploadSuccess:
		// Upload successful - client closes connection
		c.logger.Debug("Upload successful, closing connection", "file", file.Path)
		return nil
	case MsgTypeUploadError:
		var uploadError UploadError
		if err := responseMsg.UnmarshalData(&uploadError); err != nil {
			return fmt.Errorf("failed to unmarshal upload error: %w", err)
		}
		c.logger.Debug("Upload failed, closing connection", "file", file.Path, "error", uploadError.Error)
		return fmt.Errorf("upload failed: %s", uploadError.Error)
	default:
		return fmt.Errorf("unexpected response type: %s", responseMsg.Type)
	}
}

// Git helper functions

func (c *Client) isGitRepository() bool {
	gitDir := filepath.Join(c.gitRepoPath, ".git")
	if _, err := os.Stat(gitDir); err == nil {
		return true
	}

	cmd := exec.Command("git", "rev-parse", "--git-dir")
	cmd.Dir = c.gitRepoPath
	err := cmd.Run()
	return err == nil
}

func (c *Client) getTrackedFiles() ([]string, error) {
	args := []string{"ls-files"}
	if c.config.Branch != "" {
		args = append(args, fmt.Sprintf("--with-tree=%s", c.config.Branch))
	}

	cmd := exec.Command("git", args...)
	cmd.Dir = c.gitRepoPath

	output, err := cmd.Output()
	if err != nil {
		return nil, fmt.Errorf("failed to list tracked files: %w", err)
	}

	files := strings.Split(strings.TrimSpace(string(output)), "\n")
	if len(files) == 1 && files[0] == "" {
		return []string{}, nil
	}

	return files, nil
}

func (c *Client) getAllFiles() ([]string, error) {
	var files []string

	err := filepath.Walk(c.gitRepoPath, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}

		if info.IsDir() {
			if info.Name() == ".git" {
				return filepath.SkipDir
			}
			return nil
		}

		relPath, err := filepath.Rel(c.gitRepoPath, path)
		if err != nil {
			return err
		}

		files = append(files, relPath)
		return nil
	})

	return files, err
}

func calculateFileHash(filePath string) (string, error) {
	file, err := os.Open(filePath)
	if err != nil {
		return "", err
	}
	defer file.Close()

	hash := sha256.New()
	if _, err := io.Copy(hash, file); err != nil {
		return "", err
	}

	return hex.EncodeToString(hash.Sum(nil)), nil
}
