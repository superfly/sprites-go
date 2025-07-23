package sync

import (
	"context"
	"crypto/rand"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"hash"
	"io"
	"log/slog"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"time"

	"github.com/gorilla/websocket"
)

// ServerConfig holds configuration for the sync server
type ServerConfig struct {
	TargetBasePath string
	MaxConnections int
	Upgrader       websocket.Upgrader
	Logger         *slog.Logger
}

// Server handles the server-side sync operations
type Server struct {
	config   ServerConfig
	logger   *slog.Logger
	sessions map[string]*syncSession
	mu       sync.RWMutex
}

// syncSession represents an active sync session
type syncSession struct {
	targetPath     string
	files          map[string]*fileState
	channels       map[int]*channelState
	transferConns  map[int]*websocket.Conn
	mainConn       *websocket.Conn
	logger         *slog.Logger
	mu             sync.RWMutex
	completedFiles int
	totalFiles     int
}

// NewServer creates a new sync server
func NewServer(config ServerConfig) *Server {
	if config.MaxConnections <= 0 {
		config.MaxConnections = 10
	}

	if config.Upgrader.CheckOrigin == nil {
		config.Upgrader.CheckOrigin = func(r *http.Request) bool {
			return true // Allow all origins for now
		}
	}
	if config.Logger == nil {
		config.Logger = slog.Default()
	}

	return &Server{
		config:   config,
		logger:   config.Logger,
		sessions: make(map[string]*syncSession),
	}
}

// HandleWebSocket handles WebSocket connections for sync operations
func (s *Server) HandleWebSocket(w http.ResponseWriter, r *http.Request) {
	targetPath := r.URL.Query().Get("target")
	if targetPath == "" {
		http.Error(w, "target path is required", http.StatusBadRequest)
		return
	}

	// Check if this is a transfer connection
	sessionToken := r.URL.Query().Get("session_token")
	if sessionToken != "" {
		s.handleTransferConnection(w, r, sessionToken)
		return
	}

	// Handle main connection
	conn, err := s.config.Upgrader.Upgrade(w, r, nil)
	if err != nil {
		s.logger.Error("Failed to upgrade connection", "error", err)
		return
	}
	defer conn.Close()

	s.logger.Info("Main WebSocket connection established", "target", targetPath)

	if err := s.handleMainConnection(r.Context(), conn, targetPath); err != nil {
		s.logger.Error("Main connection failed", "error", err)

		errorMsg, _ := NewMessage(MsgTypeError, Error{
			Message: err.Error(),
		})
		conn.WriteJSON(errorMsg)
	}
}

// handleMainConnection handles the main coordination connection
func (s *Server) handleMainConnection(ctx context.Context, conn *websocket.Conn, targetPath string) error {
	// Resolve the target path relative to the configured base path
	resolvedTargetPath := s.resolveTargetPath(targetPath)
	s.logger.Info("Resolved sync target path", "clientTarget", targetPath, "resolvedTarget", resolvedTargetPath)

	// Ensure target directory exists
	if err := os.MkdirAll(resolvedTargetPath, 0755); err != nil {
		return fmt.Errorf("failed to create target directory: %w", err)
	}

	// Generate session token
	sessionToken, err := s.generateSessionToken()
	if err != nil {
		return fmt.Errorf("failed to generate session token: %w", err)
	}

	// Create session
	session := s.createSession(sessionToken, resolvedTargetPath, conn)
	defer s.removeSession(sessionToken)

	// Handle negotiation phase
	if err := s.handleNegotiationPhase(ctx, session, sessionToken); err != nil {
		return err
	}

	// Wait for all transfers to complete
	if err := s.waitForTransfersComplete(ctx, session); err != nil {
		return err
	}

	return nil
}

// fileState holds the state of a file being synced
type fileState struct {
	info     FileInfo
	needed   bool
	uploaded bool
}

// channelState holds the state of an upload channel
type channelState struct {
	id       int
	filePath string
	file     *os.File
	hasher   hash.Hash
	size     int64
	received int64
}

// handleNegotiationPhase handles the file negotiation phase
func (s *Server) handleNegotiationPhase(ctx context.Context, session *syncSession, sessionToken string) error {
	var filesNeeded int
	var filesSkipped int

	for {
		select {
		case <-ctx.Done():
			return ctx.Err()
		default:
		}

		var msg Message
		if err := session.mainConn.ReadJSON(&msg); err != nil {
			return fmt.Errorf("failed to read message: %w", err)
		}

		switch msg.Type {
		case MsgTypeFileInfo:
			if err := s.handleFileInfo(session, &msg); err != nil {
				return err
			}

		case MsgTypeNegotiation:
			// Count needed and skipped files
			for _, file := range session.files {
				if file.needed {
					filesNeeded++
				} else {
					filesSkipped++
				}
			}

			// Send negotiation complete with session token
			negComplete := NegotiationComplete{
				TotalFiles:   len(session.files),
				FilesNeeded:  filesNeeded,
				FilesSkipped: filesSkipped,
				Channels:     4, // Number of transfer connections
				SessionToken: sessionToken,
			}

			responseMsg, _ := NewMessage(MsgTypeNegotiation, negComplete)
			if err := session.mainConn.WriteJSON(responseMsg); err != nil {
				return err
			}

			session.totalFiles = filesNeeded
			s.logger.Info("Negotiation complete", "files_needed", filesNeeded, "session", sessionToken)
			return nil

		default:
			return fmt.Errorf("unexpected message type during negotiation: %s", msg.Type)
		}
	}
}

// handleFileInfo processes file info messages during negotiation
func (s *Server) handleFileInfo(session *syncSession, msg *Message) error {
	var fileInfo FileInfo
	if err := msg.UnmarshalData(&fileInfo); err != nil {
		return err
	}

	session.mu.Lock()
	defer session.mu.Unlock()

	// Check if file is needed
	targetFilePath := filepath.Join(session.targetPath, fileInfo.Path)
	needed := !s.fileExistsWithHash(targetFilePath, fileInfo.Hash)

	session.files[fileInfo.Path] = &fileState{
		info:   fileInfo,
		needed: needed,
	}

	// Send response
	var responseMsg *Message
	if needed {
		responseMsg, _ = NewMessage(MsgTypeFileNeeded, FileNeeded{
			Path: fileInfo.Path,
		})
	} else {
		responseMsg, _ = NewMessage(MsgTypeFileSkipped, FileSkipped{
			Path:   fileInfo.Path,
			Reason: "file exists with same hash",
		})
	}

	return session.mainConn.WriteJSON(responseMsg)
}

// handleTransferSession handles a transfer connection session
func (s *Server) handleTransferSession(ctx context.Context, conn *websocket.Conn, session *syncSession) error {
	// Wait for transfer auth message
	var authMsg Message
	if err := conn.ReadJSON(&authMsg); err != nil {
		return fmt.Errorf("failed to read auth message: %w", err)
	}

	if authMsg.Type != MsgTypeTransferAuth {
		return fmt.Errorf("expected transfer auth, got %s", authMsg.Type)
	}

	var transferAuth TransferAuth
	if err := authMsg.UnmarshalData(&transferAuth); err != nil {
		return err
	}

	// Register this connection with the session
	session.mu.Lock()
	session.transferConns[transferAuth.ChannelID] = conn
	session.channels[transferAuth.ChannelID] = &channelState{id: transferAuth.ChannelID}
	session.mu.Unlock()

	// Send ready message
	readyMsg, _ := NewMessage(MsgTypeTransferReady, TransferReady{
		ChannelID: transferAuth.ChannelID,
	})
	if err := conn.WriteJSON(readyMsg); err != nil {
		return err
	}

	s.logger.Info("Transfer channel ready", "channel", transferAuth.ChannelID)

	// Handle transfer messages
	for {
		select {
		case <-ctx.Done():
			return ctx.Err()
		default:
		}

		var msg Message
		if err := conn.ReadJSON(&msg); err != nil {
			// Check if this is a normal connection close (client closed after receiving response)
			if websocket.IsCloseError(err, websocket.CloseNormalClosure, websocket.CloseGoingAway) {
				s.logger.Debug("Client closed connection normally")
				return nil
			}
			return fmt.Errorf("failed to read transfer message: %w", err)
		}

		switch msg.Type {
		case MsgTypeUploadStart:
			if err := s.handleUploadStart(session, &msg); err != nil {
				return err
			}

		case MsgTypeFileData:
			if err := s.handleFileData(session, &msg); err != nil {
				return err
			}

		case MsgTypeUploadDone:
			if err := s.handleUploadDone(session, &msg, conn); err != nil {
				s.logger.Error("Upload done handling failed", "error", err)
				return err
			}
			s.logger.Debug("Upload done processed, success message sent, waiting for client close")
			// Success message sent, continue reading until client closes connection
			// This allows client to read the response before connection closes
			continue

		default:
			return fmt.Errorf("unexpected transfer message type: %s", msg.Type)
		}
	}
}

// handleUploadStart processes upload start messages
func (s *Server) handleUploadStart(session *syncSession, msg *Message) error {
	var uploadStart UploadStart
	if err := msg.UnmarshalData(&uploadStart); err != nil {
		return err
	}

	session.mu.Lock()
	defer session.mu.Unlock()

	// Get channel state
	channel, exists := session.channels[uploadStart.ChannelID]
	if !exists {
		return fmt.Errorf("invalid channel ID: %d", uploadStart.ChannelID)
	}

	// Create target file
	targetFilePath := filepath.Join(session.targetPath, uploadStart.Path)
	s.logger.Info("Creating file for upload", "path", targetFilePath, "relativePath", uploadStart.Path)
	dirPath := filepath.Dir(targetFilePath)
	s.logger.Debug("Creating directory", "dir", dirPath)
	if err := os.MkdirAll(dirPath, 0755); err != nil {
		s.logger.Error("Failed to create directory", "dir", dirPath, "error", err)
		return fmt.Errorf("failed to create directory: %w", err)
	}
	s.logger.Debug("Directory created successfully", "dir", dirPath)

	file, err := os.Create(targetFilePath)
	if err != nil {
		s.logger.Error("Failed to create file", "path", targetFilePath, "error", err)
		return fmt.Errorf("failed to create file: %w", err)
	}
	s.logger.Info("File created successfully", "path", targetFilePath)

	// Initialize channel state
	channel.filePath = uploadStart.Path
	channel.file = file
	channel.hasher = sha256.New()
	channel.size = uploadStart.Size
	channel.received = 0

	s.logger.Debug("Upload started", "channel", uploadStart.ChannelID, "path", uploadStart.Path)

	return nil
}

// handleFileData processes file data messages
func (s *Server) handleFileData(session *syncSession, msg *Message) error {
	var fileData FileData
	if err := msg.UnmarshalData(&fileData); err != nil {
		return err
	}

	session.mu.Lock()
	defer session.mu.Unlock()

	// Get channel state
	channel, exists := session.channels[fileData.ChannelID]
	if !exists {
		return fmt.Errorf("invalid channel ID: %d", fileData.ChannelID)
	}

	if channel.file == nil {
		return fmt.Errorf("no active upload on channel %d", fileData.ChannelID)
	}

	// Write data to file
	if _, err := channel.file.Write(fileData.Data); err != nil {
		return fmt.Errorf("failed to write file data: %w", err)
	}

	// Update hash
	channel.hasher.Write(fileData.Data)
	channel.received += int64(len(fileData.Data))

	s.logger.Debug("Wrote file data", "channel", fileData.ChannelID, "bytes", len(fileData.Data), "totalReceived", channel.received)

	return nil
}

// handleUploadDone processes upload done messages
func (s *Server) handleUploadDone(session *syncSession, msg *Message, transferConn *websocket.Conn) error {
	var uploadDone UploadDone
	if err := msg.UnmarshalData(&uploadDone); err != nil {
		return err
	}

	session.mu.Lock()
	defer session.mu.Unlock()

	// Get channel state
	channel, exists := session.channels[uploadDone.ChannelID]
	if !exists {
		return fmt.Errorf("invalid channel ID: %d", uploadDone.ChannelID)
	}

	if channel.file == nil {
		return fmt.Errorf("no active upload on channel %d", uploadDone.ChannelID)
	}

	// Close file
	channel.file.Close()
	channel.file = nil

	// Verify hash
	actualHash := hex.EncodeToString(channel.hasher.Sum(nil))
	s.logger.Info("File upload verification", "channel", uploadDone.ChannelID, "path", uploadDone.Path, "expectedHash", uploadDone.Hash, "actualHash", actualHash, "expectedSize", uploadDone.Size, "actualSize", channel.received)
	if actualHash != uploadDone.Hash {
		// Remove corrupted file
		targetFilePath := filepath.Join(session.targetPath, uploadDone.Path)
		s.logger.Error("Hash mismatch - removing file", "path", targetFilePath, "expected", uploadDone.Hash, "actual", actualHash)
		os.Remove(targetFilePath)

		errorMsg, _ := NewMessage(MsgTypeUploadError, UploadError{
			ChannelID: uploadDone.ChannelID,
			Path:      uploadDone.Path,
			Error:     fmt.Sprintf("hash mismatch: expected %s, got %s", uploadDone.Hash, actualHash),
		})
		return transferConn.WriteJSON(errorMsg)
	}

	// Verify size
	if channel.received != uploadDone.Size {
		targetFilePath := filepath.Join(session.targetPath, uploadDone.Path)
		s.logger.Error("Size mismatch - removing file", "path", targetFilePath, "expected", uploadDone.Size, "actual", channel.received)
		os.Remove(targetFilePath)

		errorMsg, _ := NewMessage(MsgTypeUploadError, UploadError{
			ChannelID: uploadDone.ChannelID,
			Path:      uploadDone.Path,
			Error:     fmt.Sprintf("size mismatch: expected %d, got %d", uploadDone.Size, channel.received),
		})
		return transferConn.WriteJSON(errorMsg)
	}

	// Mark file as uploaded
	if fileState, exists := session.files[uploadDone.Path]; exists {
		fileState.uploaded = true
	}
	session.completedFiles++

	targetFilePath := filepath.Join(session.targetPath, uploadDone.Path)
	s.logger.Info("File uploaded successfully", "channel", uploadDone.ChannelID, "path", uploadDone.Path, "fullPath", targetFilePath)

	// Send success message to client
	s.logger.Debug("Sending upload success message", "channel", uploadDone.ChannelID, "path", uploadDone.Path)
	successMsg, _ := NewMessage(MsgTypeUploadSuccess, UploadSuccess{
		ChannelID: uploadDone.ChannelID,
		Path:      uploadDone.Path,
	})
	if err := transferConn.WriteJSON(successMsg); err != nil {
		s.logger.Error("Failed to send upload success message", "error", err)
		return fmt.Errorf("failed to send upload success: %w", err)
	}
	s.logger.Debug("Upload success message sent", "channel", uploadDone.ChannelID, "path", uploadDone.Path)

	// Remove transfer connection from session tracking
	delete(session.transferConns, uploadDone.ChannelID)

	return nil
}

// waitForTransfersComplete waits for all file transfers to complete
func (s *Server) waitForTransfersComplete(ctx context.Context, session *syncSession) error {
	// If no files needed, complete immediately
	if session.totalFiles == 0 {
		completeMsg, _ := NewMessage(MsgTypeComplete, Complete{
			FilesUploaded: 0,
			FilesSkipped:  len(session.files),
			BytesUploaded: 0,
			Duration:      0,
		})
		return session.mainConn.WriteJSON(completeMsg)
	}

	// Wait for all transfers to complete
	for {
		select {
		case <-ctx.Done():
			return ctx.Err()
		default:
		}

		session.mu.RLock()
		completed := session.completedFiles
		total := session.totalFiles
		session.mu.RUnlock()

		if completed >= total {
			// All transfers complete
			var filesUploaded, filesSkipped int
			var bytesUploaded int64

			for _, file := range session.files {
				if file.needed {
					filesUploaded++
					bytesUploaded += file.info.Size
				} else {
					filesSkipped++
				}
			}

			completeMsg, _ := NewMessage(MsgTypeComplete, Complete{
				FilesUploaded: filesUploaded,
				FilesSkipped:  filesSkipped,
				BytesUploaded: bytesUploaded,
				Duration:      time.Since(time.Now()), // TODO: track actual duration
			})
			return session.mainConn.WriteJSON(completeMsg)
		}

		// Wait a bit before checking again
		time.Sleep(100 * time.Millisecond)
	}
}

// generateSessionToken generates a cryptographically secure token
func (s *Server) generateSessionToken() (string, error) {
	bytes := make([]byte, 32)
	if _, err := rand.Read(bytes); err != nil {
		return "", err
	}
	return hex.EncodeToString(bytes), nil
}

// createSession creates a new sync session
func (s *Server) createSession(token, targetPath string, conn *websocket.Conn) *syncSession {
	session := &syncSession{
		targetPath:    targetPath,
		files:         make(map[string]*fileState),
		channels:      make(map[int]*channelState),
		transferConns: make(map[int]*websocket.Conn),
		mainConn:      conn,
		logger:        s.logger,
	}

	s.mu.Lock()
	s.sessions[token] = session
	s.mu.Unlock()

	return session
}

// getSession retrieves a sync session by token
func (s *Server) getSession(token string) *syncSession {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.sessions[token]
}

// removeSession removes a sync session
func (s *Server) removeSession(token string) {
	s.mu.Lock()
	defer s.mu.Unlock()
	delete(s.sessions, token)
}

// handleTransferConnection handles transfer connections
func (s *Server) handleTransferConnection(w http.ResponseWriter, r *http.Request, sessionToken string) {
	// Get session
	session := s.getSession(sessionToken)
	if session == nil {
		http.Error(w, "invalid session token", http.StatusUnauthorized)
		return
	}

	conn, err := s.config.Upgrader.Upgrade(w, r, nil)
	if err != nil {
		s.logger.Error("Failed to upgrade transfer connection", "error", err)
		return
	}
	defer conn.Close()

	s.logger.Info("Transfer connection established", "session", sessionToken)

	// Handle transfer connection
	if err := s.handleTransferSession(r.Context(), conn, session); err != nil {
		s.logger.Error("Transfer session failed", "error", err)
		errorMsg, _ := NewMessage(MsgTypeError, Error{
			Message: err.Error(),
		})
		conn.WriteJSON(errorMsg)
	}
}

// resolveTargetPath resolves the client's target path to the actual host path
func (s *Server) resolveTargetPath(clientTargetPath string) string {
	// If the client target path is absolute, check if it needs mapping
	if filepath.IsAbs(clientTargetPath) {
		// Map guest paths to host paths
		switch clientTargetPath {
		case "/data":
			// /data in guest maps to the JuiceFS active filesystem
			return s.config.TargetBasePath
		default:
			// For other absolute paths, use them relative to the base path
			return filepath.Join(s.config.TargetBasePath, strings.TrimPrefix(clientTargetPath, "/"))
		}
	}
	// For relative paths, join with the base path
	return filepath.Join(s.config.TargetBasePath, clientTargetPath)
}

// fileExistsWithHash checks if a file exists and has the expected hash
func (s *Server) fileExistsWithHash(filePath, expectedHash string) bool {
	file, err := os.Open(filePath)
	if err != nil {
		return false
	}
	defer file.Close()

	hash := sha256.New()
	if _, err := io.Copy(hash, file); err != nil {
		return false
	}

	actualHash := hex.EncodeToString(hash.Sum(nil))
	return actualHash == expectedHash
}
