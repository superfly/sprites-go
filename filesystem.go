package sprites

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"io/fs"
	"net/http"
	"net/url"
	"path"
	"strconv"
	"time"
)

// FS provides filesystem operations on a sprite.
// It implements io/fs.FS for read operations and adds write operations.
type FS interface {
	fs.FS         // Open(name string) (fs.File, error)
	fs.StatFS     // Stat(name string) (fs.FileInfo, error)
	fs.ReadFileFS // ReadFile(name string) ([]byte, error)
	fs.ReadDirFS  // ReadDir(name string) ([]DirEntry, error)

	// Write operations
	WriteFile(name string, data []byte, perm fs.FileMode) error
	Mkdir(name string, perm fs.FileMode) error
	MkdirAll(path string, perm fs.FileMode) error
	Remove(name string) error
	RemoveAll(path string) error
	Rename(oldname, newname string) error
	Copy(src, dst string) error
	Chmod(name string, mode fs.FileMode) error

	// Context variants for long operations
	WriteFileContext(ctx context.Context, name string, data []byte, perm fs.FileMode) error
	RemoveContext(ctx context.Context, name string) error
	RemoveAllContext(ctx context.Context, path string) error
	CopyContext(ctx context.Context, src, dst string) error
	ChmodContext(ctx context.Context, name string, mode fs.FileMode) error
}

// Filesystem returns a filesystem interface for the sprite.
func (s *Sprite) Filesystem() FS {
	return &spriteFS{
		sprite:     s,
		workingDir: "/",
	}
}

// FilesystemAt returns a filesystem interface rooted at the given directory.
func (s *Sprite) FilesystemAt(workingDir string) FS {
	return &spriteFS{
		sprite:     s,
		workingDir: workingDir,
	}
}

// spriteFS implements the FS interface
type spriteFS struct {
	sprite     *Sprite
	workingDir string
}

// fsError represents a filesystem error from the server
type fsError struct {
	Error string `json:"error"`
	Code  string `json:"code,omitempty"`
	Path  string `json:"path,omitempty"`
}

// fsEntry represents a file/directory entry from the server
type fsEntry struct {
	Name    string    `json:"name"`
	Path    string    `json:"path"`
	Type    string    `json:"type"` // "file" or "directory"
	Size    int64     `json:"size"`
	Mode    string    `json:"mode"`
	ModTime time.Time `json:"modTime"`
	IsDir   bool      `json:"isDir"`
}

// fsListResponse is the response from /fs/list
type fsListResponse struct {
	Path    string    `json:"path"`
	Entries []fsEntry `json:"entries"`
	Count   int       `json:"count"`
}

// fsWriteResponse is the response from /fs/write
type fsWriteResponse struct {
	Path string `json:"path"`
	Size int64  `json:"size"`
	Mode string `json:"mode"`
}

// fsDeleteResponse is the response from /fs/delete
type fsDeleteResponse struct {
	Deleted []string `json:"deleted"`
	Count   int      `json:"count"`
}

// fsRenameRequest is the request body for /fs/rename
type fsRenameRequest struct {
	Source     string `json:"source"`
	Dest       string `json:"dest"`
	WorkingDir string `json:"workingDir"`
}

// fsCopyRequest is the request body for /fs/copy
type fsCopyRequest struct {
	Source     string `json:"source"`
	Dest       string `json:"dest"`
	WorkingDir string `json:"workingDir"`
	Recursive  bool   `json:"recursive"`
}

// fsChmodRequest is the request body for /fs/chmod
type fsChmodRequest struct {
	Path       string `json:"path"`
	WorkingDir string `json:"workingDir"`
	Mode       string `json:"mode"`
}

// Open opens a file for reading.
func (f *spriteFS) Open(name string) (fs.File, error) {
	return f.openFile(context.Background(), name)
}

func (f *spriteFS) openFile(ctx context.Context, name string) (fs.File, error) {
	// First stat to get file info
	info, err := f.statContext(ctx, name)
	if err != nil {
		return nil, err
	}

	if info.IsDir() {
		return &spriteDir{
			fs:   f,
			name: name,
			info: info,
		}, nil
	}

	// Read file content
	data, err := f.ReadFileContext(ctx, name)
	if err != nil {
		return nil, err
	}

	return &spriteFile{
		name:   name,
		info:   info,
		reader: bytes.NewReader(data),
	}, nil
}

// Stat returns file info for the named file.
func (f *spriteFS) Stat(name string) (fs.FileInfo, error) {
	return f.statContext(context.Background(), name)
}

func (f *spriteFS) statContext(ctx context.Context, name string) (fs.FileInfo, error) {
	// Use list with the specific path to get info
	u := f.buildURL("/fs/list")
	q := u.Query()
	q.Set("path", name)
	q.Set("workingDir", f.workingDir)
	u.RawQuery = q.Encode()

	req, err := http.NewRequestWithContext(ctx, "GET", u.String(), nil)
	if err != nil {
		return nil, &fs.PathError{Op: "stat", Path: name, Err: err}
	}
	f.setAuth(req)

	resp, err := f.sprite.client.httpClient.Do(req)
	if err != nil {
		return nil, &fs.PathError{Op: "stat", Path: name, Err: err}
	}
	defer resp.Body.Close()

	if resp.StatusCode == http.StatusNotFound {
		return nil, &fs.PathError{Op: "stat", Path: name, Err: fs.ErrNotExist}
	}
	if resp.StatusCode != http.StatusOK {
		var fsErr fsError
		if json.NewDecoder(resp.Body).Decode(&fsErr) == nil && fsErr.Error != "" {
			return nil, &fs.PathError{Op: "stat", Path: name, Err: fmt.Errorf("%s", fsErr.Error)}
		}
		return nil, &fs.PathError{Op: "stat", Path: name, Err: fmt.Errorf("HTTP %d", resp.StatusCode)}
	}

	var listResp fsListResponse
	if err := json.NewDecoder(resp.Body).Decode(&listResp); err != nil {
		return nil, &fs.PathError{Op: "stat", Path: name, Err: err}
	}

	if len(listResp.Entries) == 0 {
		return nil, &fs.PathError{Op: "stat", Path: name, Err: fs.ErrNotExist}
	}

	entry := listResp.Entries[0]
	return &spriteFileInfo{
		name:    path.Base(entry.Name),
		size:    entry.Size,
		mode:    parseMode(entry.Mode, entry.IsDir),
		modTime: entry.ModTime,
		isDir:   entry.IsDir,
	}, nil
}

// ReadFile reads and returns the content of the named file.
func (f *spriteFS) ReadFile(name string) ([]byte, error) {
	return f.ReadFileContext(context.Background(), name)
}

// ReadFileContext reads and returns the content of the named file with context.
func (f *spriteFS) ReadFileContext(ctx context.Context, name string) ([]byte, error) {
	u := f.buildURL("/fs/read")
	q := u.Query()
	q.Set("path", name)
	q.Set("workingDir", f.workingDir)
	u.RawQuery = q.Encode()

	req, err := http.NewRequestWithContext(ctx, "GET", u.String(), nil)
	if err != nil {
		return nil, &fs.PathError{Op: "read", Path: name, Err: err}
	}
	f.setAuth(req)

	resp, err := f.sprite.client.httpClient.Do(req)
	if err != nil {
		return nil, &fs.PathError{Op: "read", Path: name, Err: err}
	}
	defer resp.Body.Close()

	if resp.StatusCode == http.StatusNotFound {
		return nil, &fs.PathError{Op: "read", Path: name, Err: fs.ErrNotExist}
	}
	if resp.StatusCode != http.StatusOK && resp.StatusCode != http.StatusPartialContent {
		var fsErr fsError
		if json.NewDecoder(resp.Body).Decode(&fsErr) == nil && fsErr.Error != "" {
			return nil, &fs.PathError{Op: "read", Path: name, Err: fmt.Errorf("%s", fsErr.Error)}
		}
		return nil, &fs.PathError{Op: "read", Path: name, Err: fmt.Errorf("HTTP %d", resp.StatusCode)}
	}

	return io.ReadAll(resp.Body)
}

// ReadDir reads and returns the directory entries.
func (f *spriteFS) ReadDir(name string) ([]fs.DirEntry, error) {
	return f.readDirContext(context.Background(), name)
}

func (f *spriteFS) readDirContext(ctx context.Context, name string) ([]fs.DirEntry, error) {
	u := f.buildURL("/fs/list")
	q := u.Query()
	q.Set("path", name)
	q.Set("workingDir", f.workingDir)
	u.RawQuery = q.Encode()

	req, err := http.NewRequestWithContext(ctx, "GET", u.String(), nil)
	if err != nil {
		return nil, &fs.PathError{Op: "readdir", Path: name, Err: err}
	}
	f.setAuth(req)

	resp, err := f.sprite.client.httpClient.Do(req)
	if err != nil {
		return nil, &fs.PathError{Op: "readdir", Path: name, Err: err}
	}
	defer resp.Body.Close()

	if resp.StatusCode == http.StatusNotFound {
		return nil, &fs.PathError{Op: "readdir", Path: name, Err: fs.ErrNotExist}
	}
	if resp.StatusCode != http.StatusOK {
		var fsErr fsError
		if json.NewDecoder(resp.Body).Decode(&fsErr) == nil && fsErr.Error != "" {
			return nil, &fs.PathError{Op: "readdir", Path: name, Err: fmt.Errorf("%s", fsErr.Error)}
		}
		return nil, &fs.PathError{Op: "readdir", Path: name, Err: fmt.Errorf("HTTP %d", resp.StatusCode)}
	}

	var listResp fsListResponse
	if err := json.NewDecoder(resp.Body).Decode(&listResp); err != nil {
		return nil, &fs.PathError{Op: "readdir", Path: name, Err: err}
	}

	entries := make([]fs.DirEntry, len(listResp.Entries))
	for i, e := range listResp.Entries {
		entries[i] = &spriteDirEntry{
			name:  e.Name,
			isDir: e.IsDir,
			mode:  parseMode(e.Mode, e.IsDir),
			info: &spriteFileInfo{
				name:    e.Name,
				size:    e.Size,
				mode:    parseMode(e.Mode, e.IsDir),
				modTime: e.ModTime,
				isDir:   e.IsDir,
			},
		}
	}
	return entries, nil
}

// WriteFile writes data to the named file, creating it if necessary.
func (f *spriteFS) WriteFile(name string, data []byte, perm fs.FileMode) error {
	return f.WriteFileContext(context.Background(), name, data, perm)
}

// WriteFileContext writes data to the named file with context.
func (f *spriteFS) WriteFileContext(ctx context.Context, name string, data []byte, perm fs.FileMode) error {
	u := f.buildURL("/fs/write")
	q := u.Query()
	q.Set("path", name)
	q.Set("workingDir", f.workingDir)
	q.Set("mode", fmt.Sprintf("%04o", perm))
	q.Set("mkdirParents", "true")
	u.RawQuery = q.Encode()

	req, err := http.NewRequestWithContext(ctx, "PUT", u.String(), bytes.NewReader(data))
	if err != nil {
		return &fs.PathError{Op: "write", Path: name, Err: err}
	}
	f.setAuth(req)
	req.Header.Set("Content-Type", "application/octet-stream")

	resp, err := f.sprite.client.httpClient.Do(req)
	if err != nil {
		return &fs.PathError{Op: "write", Path: name, Err: err}
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK && resp.StatusCode != http.StatusCreated {
		var fsErr fsError
		if json.NewDecoder(resp.Body).Decode(&fsErr) == nil && fsErr.Error != "" {
			return &fs.PathError{Op: "write", Path: name, Err: fmt.Errorf("%s", fsErr.Error)}
		}
		return &fs.PathError{Op: "write", Path: name, Err: fmt.Errorf("HTTP %d", resp.StatusCode)}
	}

	return nil
}

// Mkdir creates a directory.
func (f *spriteFS) Mkdir(name string, perm fs.FileMode) error {
	// Use WriteFile with empty content to create a directory marker
	// The server will create the directory when mkdirParents is true
	return f.WriteFileContext(context.Background(), name+"/.keep", []byte{}, perm)
}

// MkdirAll creates a directory and all parent directories.
func (f *spriteFS) MkdirAll(name string, perm fs.FileMode) error {
	return f.Mkdir(name, perm)
}

// Remove removes the named file or empty directory.
func (f *spriteFS) Remove(name string) error {
	return f.RemoveContext(context.Background(), name)
}

// RemoveContext removes the named file or empty directory with context.
func (f *spriteFS) RemoveContext(ctx context.Context, name string) error {
	return f.removeInternal(ctx, name, false)
}

// RemoveAll removes the named file or directory and all children.
func (f *spriteFS) RemoveAll(name string) error {
	return f.RemoveAllContext(context.Background(), name)
}

// RemoveAllContext removes the named file or directory and all children with context.
func (f *spriteFS) RemoveAllContext(ctx context.Context, name string) error {
	return f.removeInternal(ctx, name, true)
}

func (f *spriteFS) removeInternal(ctx context.Context, name string, recursive bool) error {
	u := f.buildURL("/fs/delete")
	q := u.Query()
	q.Set("path", name)
	q.Set("workingDir", f.workingDir)
	if recursive {
		q.Set("recursive", "true")
	}
	u.RawQuery = q.Encode()

	req, err := http.NewRequestWithContext(ctx, "DELETE", u.String(), nil)
	if err != nil {
		return &fs.PathError{Op: "remove", Path: name, Err: err}
	}
	f.setAuth(req)

	resp, err := f.sprite.client.httpClient.Do(req)
	if err != nil {
		return &fs.PathError{Op: "remove", Path: name, Err: err}
	}
	defer resp.Body.Close()

	if resp.StatusCode == http.StatusNotFound {
		return &fs.PathError{Op: "remove", Path: name, Err: fs.ErrNotExist}
	}
	if resp.StatusCode != http.StatusOK {
		var fsErr fsError
		if json.NewDecoder(resp.Body).Decode(&fsErr) == nil && fsErr.Error != "" {
			return &fs.PathError{Op: "remove", Path: name, Err: fmt.Errorf("%s", fsErr.Error)}
		}
		return &fs.PathError{Op: "remove", Path: name, Err: fmt.Errorf("HTTP %d", resp.StatusCode)}
	}

	return nil
}

// Rename renames (moves) a file or directory.
func (f *spriteFS) Rename(oldname, newname string) error {
	return f.renameContext(context.Background(), oldname, newname)
}

func (f *spriteFS) renameContext(ctx context.Context, oldname, newname string) error {
	u := f.buildURL("/fs/rename")

	body, err := json.Marshal(fsRenameRequest{
		Source:     oldname,
		Dest:       newname,
		WorkingDir: f.workingDir,
	})
	if err != nil {
		return &fs.PathError{Op: "rename", Path: oldname, Err: err}
	}

	req, err := http.NewRequestWithContext(ctx, "POST", u.String(), bytes.NewReader(body))
	if err != nil {
		return &fs.PathError{Op: "rename", Path: oldname, Err: err}
	}
	f.setAuth(req)
	req.Header.Set("Content-Type", "application/json")

	resp, err := f.sprite.client.httpClient.Do(req)
	if err != nil {
		return &fs.PathError{Op: "rename", Path: oldname, Err: err}
	}
	defer resp.Body.Close()

	if resp.StatusCode == http.StatusNotFound {
		return &fs.PathError{Op: "rename", Path: oldname, Err: fs.ErrNotExist}
	}
	if resp.StatusCode != http.StatusOK {
		var fsErr fsError
		if json.NewDecoder(resp.Body).Decode(&fsErr) == nil && fsErr.Error != "" {
			return &fs.PathError{Op: "rename", Path: oldname, Err: fmt.Errorf("%s", fsErr.Error)}
		}
		return &fs.PathError{Op: "rename", Path: oldname, Err: fmt.Errorf("HTTP %d", resp.StatusCode)}
	}

	return nil
}

// Copy copies a file or directory to a new location.
func (f *spriteFS) Copy(src, dst string) error {
	return f.CopyContext(context.Background(), src, dst)
}

// CopyContext copies a file or directory with context.
func (f *spriteFS) CopyContext(ctx context.Context, src, dst string) error {
	u := f.buildURL("/fs/copy")

	body, err := json.Marshal(fsCopyRequest{
		Source:     src,
		Dest:       dst,
		WorkingDir: f.workingDir,
		Recursive:  true,
	})
	if err != nil {
		return &fs.PathError{Op: "copy", Path: src, Err: err}
	}

	req, err := http.NewRequestWithContext(ctx, "POST", u.String(), bytes.NewReader(body))
	if err != nil {
		return &fs.PathError{Op: "copy", Path: src, Err: err}
	}
	f.setAuth(req)
	req.Header.Set("Content-Type", "application/json")

	resp, err := f.sprite.client.httpClient.Do(req)
	if err != nil {
		return &fs.PathError{Op: "copy", Path: src, Err: err}
	}
	defer resp.Body.Close()

	if resp.StatusCode == http.StatusNotFound {
		return &fs.PathError{Op: "copy", Path: src, Err: fs.ErrNotExist}
	}
	if resp.StatusCode != http.StatusOK {
		var fsErr fsError
		if json.NewDecoder(resp.Body).Decode(&fsErr) == nil && fsErr.Error != "" {
			return &fs.PathError{Op: "copy", Path: src, Err: fmt.Errorf("%s", fsErr.Error)}
		}
		return &fs.PathError{Op: "copy", Path: src, Err: fmt.Errorf("HTTP %d", resp.StatusCode)}
	}

	return nil
}

// Chmod changes the file mode of the named file.
func (f *spriteFS) Chmod(name string, mode fs.FileMode) error {
	return f.ChmodContext(context.Background(), name, mode)
}

// ChmodContext changes the file mode with context.
func (f *spriteFS) ChmodContext(ctx context.Context, name string, mode fs.FileMode) error {
	u := f.buildURL("/fs/chmod")

	body, err := json.Marshal(fsChmodRequest{
		Path:       name,
		WorkingDir: f.workingDir,
		Mode:       fmt.Sprintf("%04o", mode&0777),
	})
	if err != nil {
		return &fs.PathError{Op: "chmod", Path: name, Err: err}
	}

	req, err := http.NewRequestWithContext(ctx, "POST", u.String(), bytes.NewReader(body))
	if err != nil {
		return &fs.PathError{Op: "chmod", Path: name, Err: err}
	}
	f.setAuth(req)
	req.Header.Set("Content-Type", "application/json")

	resp, err := f.sprite.client.httpClient.Do(req)
	if err != nil {
		return &fs.PathError{Op: "chmod", Path: name, Err: err}
	}
	defer resp.Body.Close()

	if resp.StatusCode == http.StatusNotFound {
		return &fs.PathError{Op: "chmod", Path: name, Err: fs.ErrNotExist}
	}
	if resp.StatusCode != http.StatusOK {
		var fsErr fsError
		if json.NewDecoder(resp.Body).Decode(&fsErr) == nil && fsErr.Error != "" {
			return &fs.PathError{Op: "chmod", Path: name, Err: fmt.Errorf("%s", fsErr.Error)}
		}
		return &fs.PathError{Op: "chmod", Path: name, Err: fmt.Errorf("HTTP %d", resp.StatusCode)}
	}

	return nil
}

// Helper methods

func (f *spriteFS) buildURL(path string) *url.URL {
	u, _ := url.Parse(f.sprite.client.baseURL)
	u.Path = fmt.Sprintf("/v1/sprites/%s%s", f.sprite.name, path)
	return u
}

func (f *spriteFS) setAuth(req *http.Request) {
	req.Header.Set("Authorization", fmt.Sprintf("Bearer %s", f.sprite.client.token))
}

// parseMode converts an octal mode string to fs.FileMode
func parseMode(mode string, isDir bool) fs.FileMode {
	m, err := strconv.ParseUint(mode, 8, 32)
	if err != nil {
		if isDir {
			return fs.ModeDir | 0755
		}
		return 0644
	}
	fm := fs.FileMode(m)
	if isDir {
		fm |= fs.ModeDir
	}
	return fm
}

// spriteFileInfo implements fs.FileInfo
type spriteFileInfo struct {
	name    string
	size    int64
	mode    fs.FileMode
	modTime time.Time
	isDir   bool
}

func (fi *spriteFileInfo) Name() string       { return fi.name }
func (fi *spriteFileInfo) Size() int64        { return fi.size }
func (fi *spriteFileInfo) Mode() fs.FileMode  { return fi.mode }
func (fi *spriteFileInfo) ModTime() time.Time { return fi.modTime }
func (fi *spriteFileInfo) IsDir() bool        { return fi.isDir }
func (fi *spriteFileInfo) Sys() any           { return nil }

// spriteDirEntry implements fs.DirEntry
type spriteDirEntry struct {
	name  string
	isDir bool
	mode  fs.FileMode
	info  fs.FileInfo
}

func (de *spriteDirEntry) Name() string               { return de.name }
func (de *spriteDirEntry) IsDir() bool                { return de.isDir }
func (de *spriteDirEntry) Type() fs.FileMode          { return de.mode.Type() }
func (de *spriteDirEntry) Info() (fs.FileInfo, error) { return de.info, nil }

// spriteFile implements fs.File for regular files
type spriteFile struct {
	name   string
	info   fs.FileInfo
	reader *bytes.Reader
}

func (f *spriteFile) Stat() (fs.FileInfo, error) { return f.info, nil }
func (f *spriteFile) Read(b []byte) (int, error) { return f.reader.Read(b) }
func (f *spriteFile) Close() error               { return nil }

// spriteDir implements fs.File for directories
type spriteDir struct {
	fs      *spriteFS
	name    string
	info    fs.FileInfo
	entries []fs.DirEntry
	offset  int
}

func (d *spriteDir) Stat() (fs.FileInfo, error) { return d.info, nil }
func (d *spriteDir) Read(b []byte) (int, error) { return 0, &fs.PathError{Op: "read", Path: d.name, Err: fs.ErrInvalid} }
func (d *spriteDir) Close() error               { return nil }

// ReadDir implements fs.ReadDirFile
func (d *spriteDir) ReadDir(n int) ([]fs.DirEntry, error) {
	if d.entries == nil {
		entries, err := d.fs.ReadDir(d.name)
		if err != nil {
			return nil, err
		}
		d.entries = entries
	}

	if n <= 0 {
		entries := d.entries[d.offset:]
		d.offset = len(d.entries)
		return entries, nil
	}

	if d.offset >= len(d.entries) {
		return nil, io.EOF
	}

	end := d.offset + n
	if end > len(d.entries) {
		end = len(d.entries)
	}
	entries := d.entries[d.offset:end]
	d.offset = end
	return entries, nil
}
