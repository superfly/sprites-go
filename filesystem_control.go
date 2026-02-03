package sprites

import (
	"context"
	"encoding/json"
	"fmt"
	"io/fs"
	"net/url"
	"path"
	"strconv"
	"time"

	"github.com/gorilla/websocket"
)

// FsControlOption is a functional option for filesystem control operations
type FsControlOption func(*fsControlOpts)

type fsControlOpts struct {
	workingDir    string
	mode          fs.FileMode
	mkdirParents  bool
	asRoot        bool
	recursive     bool
	preserveAttrs bool
	uid           int
	gid           int
	start         int64
	end           int64
}

// WithFsWorkingDir sets the working directory for path resolution
func WithFsWorkingDir(dir string) FsControlOption {
	return func(o *fsControlOpts) {
		o.workingDir = dir
	}
}

// WithFsMode sets the file mode for write operations
func WithFsMode(mode fs.FileMode) FsControlOption {
	return func(o *fsControlOpts) {
		o.mode = mode
	}
}

// WithFsMkdirParents enables automatic parent directory creation
func WithFsMkdirParents(enable bool) FsControlOption {
	return func(o *fsControlOpts) {
		o.mkdirParents = enable
	}
}

// WithFsAsRoot runs the operation as root user
func WithFsAsRoot(enable bool) FsControlOption {
	return func(o *fsControlOpts) {
		o.asRoot = enable
	}
}

// WithFsRecursive enables recursive operation
func WithFsRecursive(enable bool) FsControlOption {
	return func(o *fsControlOpts) {
		o.recursive = enable
	}
}

// WithFsPreserveAttrs preserves file attributes during copy
func WithFsPreserveAttrs(enable bool) FsControlOption {
	return func(o *fsControlOpts) {
		o.preserveAttrs = enable
	}
}

// WithFsUid sets the user ID for chown operations
func WithFsUid(uid int) FsControlOption {
	return func(o *fsControlOpts) {
		o.uid = uid
	}
}

// WithFsGid sets the group ID for chown operations
func WithFsGid(gid int) FsControlOption {
	return func(o *fsControlOpts) {
		o.gid = gid
	}
}

// WithFsRange sets the byte range for read operations
func WithFsRange(start, end int64) FsControlOption {
	return func(o *fsControlOpts) {
		o.start = start
		o.end = end
	}
}

// FsReadResult contains the result of a fs.read operation
type FsReadResult struct {
	Path string `json:"path"`
	Size int64  `json:"size"`
	Data []byte `json:"-"`
}

// FsWriteResult contains the result of a fs.write operation
type FsWriteResult struct {
	Path string `json:"path"`
	Size int64  `json:"size"`
	Mode string `json:"mode"`
}

// FsListResult contains the result of a fs.list operation
type FsListResult struct {
	Path    string    `json:"path"`
	Entries []FsEntry `json:"entries"`
	Count   int       `json:"count"`
}

// FsEntry represents a file or directory entry
type FsEntry struct {
	Name    string    `json:"name"`
	Path    string    `json:"path"`
	Type    string    `json:"type"`
	Size    int64     `json:"size"`
	Mode    string    `json:"mode"`
	ModTime time.Time `json:"modTime"`
	IsDir   bool      `json:"isDir"`
}

// FsDeleteResult contains the result of a fs.delete operation
type FsDeleteResult struct {
	Deleted []string `json:"deleted"`
	Count   int      `json:"count"`
}

// FsChmodResult contains the result of a fs.chmod operation
type FsChmodResult struct {
	Affected []FsChmodEntry `json:"affected"`
	Count    int            `json:"count"`
}

// FsChmodEntry represents a single chmod result
type FsChmodEntry struct {
	Path string `json:"path"`
	Mode string `json:"mode"`
}

// FsChownResult contains the result of a fs.chown operation
type FsChownResult struct {
	Affected []FsChownEntry `json:"affected"`
	Count    int            `json:"count"`
}

// FsChownEntry represents a single chown result
type FsChownEntry struct {
	Path string `json:"path"`
	UID  int    `json:"uid"`
	GID  int    `json:"gid"`
}

// FsCopyResult contains the result of a fs.copy operation
type FsCopyResult struct {
	Copied     []FsCopyEntry `json:"copied"`
	Count      int           `json:"count"`
	TotalBytes int64         `json:"totalBytes"`
}

// FsCopyEntry represents a single copy result
type FsCopyEntry struct {
	Source string `json:"source"`
	Dest   string `json:"dest"`
}

// FsRenameResult contains the result of a fs.rename operation
type FsRenameResult struct {
	Source string `json:"source"`
	Dest   string `json:"dest"`
}

// FsErrorResponse represents a filesystem operation error
type FsErrorResponse struct {
	Error string `json:"error"`
	Code  string `json:"code,omitempty"`
	Path  string `json:"path,omitempty"`
}

// FsReadControl reads a file using the control channel
func (s *Sprite) FsReadControl(ctx context.Context, filePath string, opts ...FsControlOption) (*FsReadResult, error) {
	o := &fsControlOpts{
		workingDir: "/home/sprite",
	}
	for _, opt := range opts {
		opt(o)
	}

	// Build args
	args := url.Values{}
	args.Set("path", filePath)
	if o.workingDir != "" {
		args.Set("workingDir", o.workingDir)
	}
	if o.start > 0 {
		args.Set("start", strconv.FormatInt(o.start, 10))
	}
	if o.end > 0 {
		args.Set("end", strconv.FormatInt(o.end, 10))
	}

	// Execute operation
	conn, err := s.checkoutControlConn(ctx)
	if err != nil {
		return nil, err
	}
	defer s.checkinControlConn(conn)

	if err := s.sendControlOp(conn, "fs.read", args); err != nil {
		return nil, err
	}

	// Read JSON response first
	_, data, err := conn.ws.ReadMessage()
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	// Check for error response
	var errResp FsErrorResponse
	if json.Unmarshal(data, &errResp) == nil && errResp.Error != "" {
		return nil, &fs.PathError{Op: "read", Path: filePath, Err: fmt.Errorf("%s (%s)", errResp.Error, errResp.Code)}
	}

	var result FsReadResult
	if err := json.Unmarshal(data, &result); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	// Read binary data
	msgType, binaryData, err := conn.ws.ReadMessage()
	if err != nil {
		return nil, fmt.Errorf("failed to read file data: %w", err)
	}
	if msgType != websocket.BinaryMessage {
		return nil, fmt.Errorf("expected binary data, got type %d", msgType)
	}

	result.Data = binaryData

	// Wait for op.complete
	if err := s.waitControlComplete(conn); err != nil {
		return nil, err
	}

	return &result, nil
}

// FsWriteControl writes a file using the control channel
func (s *Sprite) FsWriteControl(ctx context.Context, filePath string, data []byte, opts ...FsControlOption) (*FsWriteResult, error) {
	o := &fsControlOpts{
		workingDir:   "/home/sprite",
		mode:         0644,
		mkdirParents: true,
	}
	for _, opt := range opts {
		opt(o)
	}

	// Build args
	args := url.Values{}
	args.Set("path", filePath)
	if o.workingDir != "" {
		args.Set("workingDir", o.workingDir)
	}
	args.Set("mode", fmt.Sprintf("%04o", o.mode))
	if !o.mkdirParents {
		args.Set("mkdirParents", "false")
	}
	if o.asRoot {
		args.Set("asRoot", "true")
	}

	// Execute operation
	conn, err := s.checkoutControlConn(ctx)
	if err != nil {
		return nil, err
	}
	defer s.checkinControlConn(conn)

	if err := s.sendControlOp(conn, "fs.write", args); err != nil {
		return nil, err
	}

	// Send binary data
	if err := conn.ws.WriteMessage(websocket.BinaryMessage, data); err != nil {
		return nil, fmt.Errorf("failed to send data: %w", err)
	}

	// Read response
	_, respData, err := conn.ws.ReadMessage()
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	// Check for error response
	var errResp FsErrorResponse
	if json.Unmarshal(respData, &errResp) == nil && errResp.Error != "" {
		return nil, &fs.PathError{Op: "write", Path: filePath, Err: fmt.Errorf("%s (%s)", errResp.Error, errResp.Code)}
	}

	var result FsWriteResult
	if err := json.Unmarshal(respData, &result); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	// Wait for op.complete
	if err := s.waitControlComplete(conn); err != nil {
		return nil, err
	}

	return &result, nil
}

// FsListControl lists directory contents using the control channel
func (s *Sprite) FsListControl(ctx context.Context, dirPath string, opts ...FsControlOption) (*FsListResult, error) {
	o := &fsControlOpts{
		workingDir: "/home/sprite",
	}
	for _, opt := range opts {
		opt(o)
	}

	// Build args
	args := url.Values{}
	if dirPath != "" {
		args.Set("path", dirPath)
	}
	if o.workingDir != "" {
		args.Set("workingDir", o.workingDir)
	}
	if o.recursive {
		args.Set("recursive", "true")
	}

	// Execute operation
	conn, err := s.checkoutControlConn(ctx)
	if err != nil {
		return nil, err
	}
	defer s.checkinControlConn(conn)

	if err := s.sendControlOp(conn, "fs.list", args); err != nil {
		return nil, err
	}

	// Read response
	_, respData, err := conn.ws.ReadMessage()
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	// Check for error response
	var errResp FsErrorResponse
	if json.Unmarshal(respData, &errResp) == nil && errResp.Error != "" {
		return nil, &fs.PathError{Op: "list", Path: dirPath, Err: fmt.Errorf("%s (%s)", errResp.Error, errResp.Code)}
	}

	var result FsListResult
	if err := json.Unmarshal(respData, &result); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	// Wait for op.complete
	if err := s.waitControlComplete(conn); err != nil {
		return nil, err
	}

	return &result, nil
}

// FsDeleteControl deletes a file or directory using the control channel
func (s *Sprite) FsDeleteControl(ctx context.Context, filePath string, opts ...FsControlOption) (*FsDeleteResult, error) {
	o := &fsControlOpts{
		workingDir: "/home/sprite",
	}
	for _, opt := range opts {
		opt(o)
	}

	// Build args
	args := url.Values{}
	args.Set("path", filePath)
	if o.workingDir != "" {
		args.Set("workingDir", o.workingDir)
	}
	if o.recursive {
		args.Set("recursive", "true")
	}

	// Execute operation
	conn, err := s.checkoutControlConn(ctx)
	if err != nil {
		return nil, err
	}
	defer s.checkinControlConn(conn)

	if err := s.sendControlOp(conn, "fs.delete", args); err != nil {
		return nil, err
	}

	// Read response
	_, respData, err := conn.ws.ReadMessage()
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	// Check for error response
	var errResp FsErrorResponse
	if json.Unmarshal(respData, &errResp) == nil && errResp.Error != "" {
		return nil, &fs.PathError{Op: "delete", Path: filePath, Err: fmt.Errorf("%s (%s)", errResp.Error, errResp.Code)}
	}

	var result FsDeleteResult
	if err := json.Unmarshal(respData, &result); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	// Wait for op.complete
	if err := s.waitControlComplete(conn); err != nil {
		return nil, err
	}

	return &result, nil
}

// FsChmodControl changes file permissions using the control channel
func (s *Sprite) FsChmodControl(ctx context.Context, filePath string, mode fs.FileMode, opts ...FsControlOption) (*FsChmodResult, error) {
	o := &fsControlOpts{
		workingDir: "/home/sprite",
	}
	for _, opt := range opts {
		opt(o)
	}

	// Build args
	args := url.Values{}
	args.Set("path", filePath)
	args.Set("mode", fmt.Sprintf("%04o", mode))
	if o.workingDir != "" {
		args.Set("workingDir", o.workingDir)
	}
	if o.recursive {
		args.Set("recursive", "true")
	}

	// Execute operation
	conn, err := s.checkoutControlConn(ctx)
	if err != nil {
		return nil, err
	}
	defer s.checkinControlConn(conn)

	if err := s.sendControlOp(conn, "fs.chmod", args); err != nil {
		return nil, err
	}

	// Read response
	_, respData, err := conn.ws.ReadMessage()
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	// Check for error response
	var errResp FsErrorResponse
	if json.Unmarshal(respData, &errResp) == nil && errResp.Error != "" {
		return nil, &fs.PathError{Op: "chmod", Path: filePath, Err: fmt.Errorf("%s (%s)", errResp.Error, errResp.Code)}
	}

	var result FsChmodResult
	if err := json.Unmarshal(respData, &result); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	// Wait for op.complete
	if err := s.waitControlComplete(conn); err != nil {
		return nil, err
	}

	return &result, nil
}

// FsChownControl changes file ownership using the control channel
func (s *Sprite) FsChownControl(ctx context.Context, filePath string, opts ...FsControlOption) (*FsChownResult, error) {
	o := &fsControlOpts{
		workingDir: "/home/sprite",
		uid:        -1,
		gid:        -1,
	}
	for _, opt := range opts {
		opt(o)
	}

	if o.uid == -1 && o.gid == -1 {
		return nil, fmt.Errorf("at least one of uid or gid must be set")
	}

	// Build args
	args := url.Values{}
	args.Set("path", filePath)
	if o.workingDir != "" {
		args.Set("workingDir", o.workingDir)
	}
	if o.uid != -1 {
		args.Set("uid", strconv.Itoa(o.uid))
	}
	if o.gid != -1 {
		args.Set("gid", strconv.Itoa(o.gid))
	}
	if o.recursive {
		args.Set("recursive", "true")
	}

	// Execute operation
	conn, err := s.checkoutControlConn(ctx)
	if err != nil {
		return nil, err
	}
	defer s.checkinControlConn(conn)

	if err := s.sendControlOp(conn, "fs.chown", args); err != nil {
		return nil, err
	}

	// Read response
	_, respData, err := conn.ws.ReadMessage()
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	// Check for error response
	var errResp FsErrorResponse
	if json.Unmarshal(respData, &errResp) == nil && errResp.Error != "" {
		return nil, &fs.PathError{Op: "chown", Path: filePath, Err: fmt.Errorf("%s (%s)", errResp.Error, errResp.Code)}
	}

	var result FsChownResult
	if err := json.Unmarshal(respData, &result); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	// Wait for op.complete
	if err := s.waitControlComplete(conn); err != nil {
		return nil, err
	}

	return &result, nil
}

// FsCopyControl copies files using the control channel
func (s *Sprite) FsCopyControl(ctx context.Context, source, dest string, opts ...FsControlOption) (*FsCopyResult, error) {
	o := &fsControlOpts{
		workingDir: "/home/sprite",
	}
	for _, opt := range opts {
		opt(o)
	}

	// Build args
	args := url.Values{}
	args.Set("source", source)
	args.Set("dest", dest)
	if o.workingDir != "" {
		args.Set("workingDir", o.workingDir)
	}
	if o.recursive {
		args.Set("recursive", "true")
	}
	if o.preserveAttrs {
		args.Set("preserveAttrs", "true")
	}
	if o.asRoot {
		args.Set("asRoot", "true")
	}

	// Execute operation
	conn, err := s.checkoutControlConn(ctx)
	if err != nil {
		return nil, err
	}
	defer s.checkinControlConn(conn)

	if err := s.sendControlOp(conn, "fs.copy", args); err != nil {
		return nil, err
	}

	// Read response
	_, respData, err := conn.ws.ReadMessage()
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	// Check for error response
	var errResp FsErrorResponse
	if json.Unmarshal(respData, &errResp) == nil && errResp.Error != "" {
		return nil, &fs.PathError{Op: "copy", Path: source, Err: fmt.Errorf("%s (%s)", errResp.Error, errResp.Code)}
	}

	var result FsCopyResult
	if err := json.Unmarshal(respData, &result); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	// Wait for op.complete
	if err := s.waitControlComplete(conn); err != nil {
		return nil, err
	}

	return &result, nil
}

// FsRenameControl renames/moves a file using the control channel
func (s *Sprite) FsRenameControl(ctx context.Context, source, dest string, opts ...FsControlOption) (*FsRenameResult, error) {
	o := &fsControlOpts{
		workingDir: "/home/sprite",
	}
	for _, opt := range opts {
		opt(o)
	}

	// Build args
	args := url.Values{}
	args.Set("source", source)
	args.Set("dest", dest)
	if o.workingDir != "" {
		args.Set("workingDir", o.workingDir)
	}

	// Execute operation
	conn, err := s.checkoutControlConn(ctx)
	if err != nil {
		return nil, err
	}
	defer s.checkinControlConn(conn)

	if err := s.sendControlOp(conn, "fs.rename", args); err != nil {
		return nil, err
	}

	// Read response
	_, respData, err := conn.ws.ReadMessage()
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	// Check for error response
	var errResp FsErrorResponse
	if json.Unmarshal(respData, &errResp) == nil && errResp.Error != "" {
		return nil, &fs.PathError{Op: "rename", Path: source, Err: fmt.Errorf("%s (%s)", errResp.Error, errResp.Code)}
	}

	var result FsRenameResult
	if err := json.Unmarshal(respData, &result); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	// Wait for op.complete
	if err := s.waitControlComplete(conn); err != nil {
		return nil, err
	}

	return &result, nil
}

// FsStatControl returns file info using the control channel (via fs.list)
func (s *Sprite) FsStatControl(ctx context.Context, filePath string, opts ...FsControlOption) (*FsEntry, error) {
	result, err := s.FsListControl(ctx, filePath, opts...)
	if err != nil {
		return nil, err
	}

	if len(result.Entries) == 0 {
		return nil, &fs.PathError{Op: "stat", Path: filePath, Err: fs.ErrNotExist}
	}

	// Return info for the path itself (first entry for the path)
	entry := result.Entries[0]
	if entry.Path == result.Path || entry.Name == path.Base(filePath) {
		return &entry, nil
	}

	// If listing a directory, return the directory info
	return &FsEntry{
		Name:  path.Base(result.Path),
		Path:  result.Path,
		IsDir: true,
		Type:  "directory",
	}, nil
}

// Helper methods for control channel operations

func (s *Sprite) checkoutControlConn(ctx context.Context) (*controlConn, error) {
	if !s.supportsControl {
		return nil, fmt.Errorf("sprite does not support control connections")
	}

	pool := s.client.getOrCreatePool(s.name)
	return pool.checkout(ctx)
}

func (s *Sprite) checkinControlConn(conn *controlConn) {
	if conn == nil {
		return
	}
	// Send release message
	conn.sendRelease()

	pool := s.client.getOrCreatePool(s.name)
	pool.checkin(conn)
}

func (s *Sprite) sendControlOp(conn *controlConn, op string, args url.Values) error {
	// Build op.start message
	msg := map[string]interface{}{
		"type": "op.start",
		"op":   op,
		"args": args.Encode(),
	}

	return conn.ws.WriteJSON(msg)
}

func (s *Sprite) waitControlComplete(conn *controlConn) error {
	// Read until we get op.complete or op.error
	for {
		_, data, err := conn.ws.ReadMessage()
		if err != nil {
			return fmt.Errorf("failed to read control message: %w", err)
		}

		var msg struct {
			Type string          `json:"type"`
			Args json.RawMessage `json:"args,omitempty"`
		}
		if err := json.Unmarshal(data, &msg); err != nil {
			continue // Not a control message
		}

		switch msg.Type {
		case "op.complete":
			return nil
		case "op.error":
			var errArgs struct {
				Error string `json:"error"`
			}
			if json.Unmarshal(msg.Args, &errArgs) == nil {
				return fmt.Errorf("operation failed: %s", errArgs.Error)
			}
			return fmt.Errorf("operation failed")
		}
	}
}
