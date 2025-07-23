package sync

import (
	"context"
	"fmt"
	"net/http"
	"net/url"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/gorilla/websocket"
)

// negotiateFilesStreaming performs streaming file negotiation
func (c *Client) negotiateFilesStreaming(ctx context.Context, conn *websocket.Conn, fileChan <-chan FileInfo, transferChan chan<- FileInfo) error {
	c.logger.Info("Starting file negotiation")

	for file := range fileChan {
		c.logger.Debug("preparing to negotiate", "file", file)

		select {
		case <-ctx.Done():
			return ctx.Err()
		default:
		}

		// Send file info to server
		msg, err := NewMessage(MsgTypeFileInfo, file)
		if err != nil {
			return fmt.Errorf("failed to create file info message: %w", err)
		}

		if err := conn.WriteJSON(msg); err != nil {
			return fmt.Errorf("failed to send file info: %w", err)
		}
		c.logger.Debug("Sent file info to server", "file", file)

		// Wait for server response
		var response Message
		if err := conn.ReadJSON(&response); err != nil {
			return fmt.Errorf("failed to read response: %w", err)
		}
		c.logger.Debug("Received negotiation response", "type", response.Type)

		switch response.Type {
		case MsgTypeFileNeeded:
			// File needed - send to transfer stage
			select {
			case transferChan <- file:
				c.logger.Debug("File needed for transfer", "path", file.Path)
			case <-ctx.Done():
				return ctx.Err()
			}

		case MsgTypeFileSkipped:
			// File skipped - continue
			c.logger.Debug("File skipped", "path", file.Path)

		case MsgTypeError:
			var errData Error
			if err := response.UnmarshalData(&errData); err != nil {
				return fmt.Errorf("failed to unmarshal error: %w", err)
			}
			return fmt.Errorf("server error: %s", errData.Message)

		default:
			return fmt.Errorf("unexpected response type: %s", response.Type)
		}
	}

	// Send negotiation complete and wait for session token
	negMsg, _ := NewMessage(MsgTypeNegotiation, nil)
	if err := conn.WriteJSON(negMsg); err != nil {
		return fmt.Errorf("failed to send negotiation complete: %w", err)
	}
	c.logger.Debug("Sent final negotiation request")

	// Wait for negotiation complete response with session token
	var response Message
	if err := conn.ReadJSON(&response); err != nil {
		return fmt.Errorf("failed to read negotiation response: %w", err)
	}
	c.logger.Debug("Received final negotiation response", "type", response.Type)

	if response.Type != MsgTypeNegotiation {
		return fmt.Errorf("expected negotiation complete, got %s", response.Type)
	}

	var negComplete NegotiationComplete
	if err := response.UnmarshalData(&negComplete); err != nil {
		return err
	}

	// Store session token for transfer connections
	c.sessionToken = negComplete.SessionToken

	c.logger.Info("File negotiation completed", "session_token", c.sessionToken, "files_needed", negComplete.FilesNeeded)
	return nil
}

// transferFilesWithOwnConnection transfers files using a dedicated connection per worker
func (c *Client) transferFilesWithOwnConnection(
	ctx context.Context,
	transferChan <-chan FileInfo,
	workerID int,
) error {
	c.logger.Info(
		"Starting file transfer worker with dedicated connection",
		"worker", workerID,
	)

	var transferConn *websocket.Conn
	for file := range transferChan {
		select {
		case <-ctx.Done():
			if transferConn != nil {
				transferConn.Close()
			}
			return ctx.Err()
		default:
		}

		if transferConn == nil {
			for c.sessionToken == "" {
				select {
				case <-ctx.Done():
					return ctx.Err()
				default:
				}
				time.Sleep(10 * time.Millisecond)
			}
			var err error
			transferConn, err = c.connectTransfer(c.sessionToken, workerID)
			if err != nil {
				return fmt.Errorf(
					"failed to create transfer connection: %w",
					err,
				)
			}
			c.logger.Info(
				"Transfer connection established",
				"worker", workerID,
			)
		}

		c.logger.Debug(
			"Transferring file",
			"worker", workerID,
			"path", file.Path,
		)

		if err := c.uploadFile(ctx, transferConn, file, workerID); err != nil {
			return fmt.Errorf("failed to upload file %s: %w", file.Path, err)
		}

		if c.config.ProgressCallback != nil {
			c.config.ProgressCallback(
				Progress{
					FilesProcessed: 1,
					BytesUploaded:  file.Size,
				},
			)
		}
	}

	if transferConn != nil {
		transferConn.Close()
	}
	c.logger.Info(
		"File transfer worker completed",
		"worker", workerID,
	)
	return nil
}

// getFilesToWalk returns files to walk (including .git)
func (c *Client) getFilesToWalk() ([]string, error) {
	var files []string

	if c.config.IncludeUncommitted {
		// Get all files in the repository (including .git)
		allFiles, err := c.getAllFilesIncludingGit()
		if err != nil {
			return nil, err
		}
		files = allFiles
	} else {
		// Get only tracked files, plus .git directory
		trackedFiles, err := c.getTrackedFiles()
		if err != nil {
			return nil, err
		}
		files = append(files, trackedFiles...)

		// Add .git directory
		gitFiles, err := c.getGitFiles()
		if err != nil {
			return nil, err
		}
		files = append(files, gitFiles...)
	}

	return files, nil
}

// getAllFilesIncludingGit returns all files in the repository (including .git)
func (c *Client) getAllFilesIncludingGit() ([]string, error) {
	var files []string

	err := filepath.Walk(c.gitRepoPath, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}

		if info.IsDir() {
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

// getGitFiles returns files in the .git directory
func (c *Client) getGitFiles() ([]string, error) {
	var files []string
	gitDir := filepath.Join(c.gitRepoPath, ".git")

	err := filepath.Walk(gitDir, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}

		if info.IsDir() {
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

// connectTransfer creates a transfer connection with authentication
func (c *Client) connectTransfer(sessionToken string, channelID int) (*websocket.Conn, error) {
	u, err := url.Parse(c.serverURL)
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

	// Add sync endpoint with session token
	u.Path = strings.TrimSuffix(u.Path, "/") + "/sync"
	queryValues := url.Values{}
	queryValues.Set("target", c.config.TargetPath)
	queryValues.Set("session_token", sessionToken)
	u.RawQuery = queryValues.Encode()

	// Create request headers
	headers := http.Header{}
	headers.Set("Authorization", "Bearer "+c.token)

	// Connect
	conn, _, err := websocket.DefaultDialer.Dial(u.String(), headers)
	if err != nil {
		return nil, err
	}

	// Send transfer auth
	authMsg, _ := NewMessage(MsgTypeTransferAuth, TransferAuth{
		SessionToken: sessionToken,
		ChannelID:    channelID,
	})
	if err := conn.WriteJSON(authMsg); err != nil {
		conn.Close()
		return nil, err
	}

	// Wait for ready response
	var response Message
	if err := conn.ReadJSON(&response); err != nil {
		conn.Close()
		return nil, err
	}

	if response.Type != MsgTypeTransferReady {
		conn.Close()
		return nil, fmt.Errorf("expected transfer ready, got %s", response.Type)
	}

	return conn, nil
}

// waitForCompletion waits for the completion message on the main connection
func (c *Client) waitForCompletion(ctx context.Context) error {
	c.logger.Info("Waiting for sync completion")

	for {
		select {
		case <-ctx.Done():
			return ctx.Err()
		default:
		}

		var msg Message
		if err := c.mainConn.ReadJSON(&msg); err != nil {
			return fmt.Errorf("failed to read completion message: %w", err)
		}
		c.logger.Debug("Completion wait got message", "type", msg.Type)

		switch msg.Type {
		case MsgTypeComplete:
			var complete Complete
			if err := msg.UnmarshalData(&complete); err != nil {
				return err
			}

			c.logger.Info("Sync completed",
				"files_uploaded", complete.FilesUploaded,
				"files_skipped", complete.FilesSkipped,
				"bytes_uploaded", complete.BytesUploaded)
			return nil

		case MsgTypeError:
			var errData Error
			if err := msg.UnmarshalData(&errData); err != nil {
				return fmt.Errorf("failed to unmarshal error: %w", err)
			}
			return fmt.Errorf("server error: %s", errData.Message)

		default:
			c.logger.Debug("Unexpected message during completion wait", "type", msg.Type)
		}
	}
}
