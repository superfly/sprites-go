package sprites

import (
	"encoding/json"
	"errors"
	"io/fs"
	"net/http"
	"net/http/httptest"
	"path"
	"strings"
	"testing"
	"time"
)

// fakeListServer mimics the server's /fs/list: a directory lists its children,
// a file lists itself, and a missing path is a 404.
func fakeListServer(t *testing.T, tree map[string]fsEntry) *httptest.Server {
	t.Helper()
	return httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if !strings.HasSuffix(r.URL.Path, "/fs/list") {
			http.NotFound(w, r)
			return
		}
		p := r.URL.Query().Get("path")
		if !path.IsAbs(p) {
			p = path.Join(r.URL.Query().Get("workingDir"), p)
		}
		p = path.Clean(p)

		self, ok := tree[p]
		if p != "/" && !ok {
			w.WriteHeader(http.StatusNotFound)
			_ = json.NewEncoder(w).Encode(fsError{Error: "no such file or directory", Path: p})
			return
		}

		entries := []fsEntry{}
		if p != "/" && !self.IsDir {
			entries = append(entries, self)
		} else {
			for childPath, e := range tree {
				if path.Dir(childPath) == p && childPath != p {
					entries = append(entries, e)
				}
			}
		}
		_ = json.NewEncoder(w).Encode(fsListResponse{Path: p, Entries: entries, Count: len(entries)})
	}))
}

func dirEntry(p string) fsEntry {
	return fsEntry{Name: path.Base(p), Path: p, Type: "directory", Mode: "0755", IsDir: true, ModTime: time.Unix(1, 0)}
}

func fileEntry(p string, size int64) fsEntry {
	return fsEntry{Name: path.Base(p), Path: p, Type: "file", Mode: "0644", Size: size, ModTime: time.Unix(2, 0)}
}

func testFS(t *testing.T, tree map[string]fsEntry, workingDir string) FS {
	t.Helper()
	srv := fakeListServer(t, tree)
	t.Cleanup(srv.Close)
	// Built directly rather than via Client.Sprite, which dials a control
	// connection the fake server does not provide.
	s := &Sprite{name: "test", client: New("tok", WithBaseURL(srv.URL))}

	return s.FilesystemAt(workingDir)
}

func TestStat(t *testing.T) {
	tree := map[string]fsEntry{
		"/tmp":                  dirEntry("/tmp"),
		"/home":                 dirEntry("/home"),
		"/home/sprite":          dirEntry("/home/sprite"),
		"/home/sprite/bin":      dirEntry("/home/sprite/bin"),
		"/home/sprite/app.txt":  fileEntry("/home/sprite/app.txt", 42),
		"/home/sprite/src":      dirEntry("/home/sprite/src"),
		"/home/sprite/src/a.go": fileEntry("/home/sprite/src/a.go", 7),
	}
	fsys := testFS(t, tree, "/home/sprite")

	tests := []struct {
		name    string
		path    string
		wantDir bool
		want    string // expected Name()
		size    int64
	}{
		// An empty directory lists no children. It must still stat as itself.
		{name: "empty dir", path: "/tmp", wantDir: true, want: "tmp"},
		{name: "empty dir relative", path: "bin", wantDir: true, want: "bin"},
		// A non-empty directory must report its own info, not its first child's.
		{name: "non-empty dir", path: "/home/sprite/src", wantDir: true, want: "src"},
		{name: "file", path: "/home/sprite/app.txt", want: "app.txt", size: 42},
		{name: "file relative", path: "src/a.go", want: "a.go", size: 7},
		{name: "root", path: "/", wantDir: true, want: "/"},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			info, err := fsys.Stat(tt.path)
			if err != nil {
				t.Fatalf("Stat(%q): %v", tt.path, err)
			}
			if info.IsDir() != tt.wantDir {
				t.Errorf("IsDir() = %v, want %v", info.IsDir(), tt.wantDir)
			}
			if info.Name() != tt.want {
				t.Errorf("Name() = %q, want %q", info.Name(), tt.want)
			}
			if !tt.wantDir && info.Size() != tt.size {
				t.Errorf("Size() = %d, want %d", info.Size(), tt.size)
			}
		})
	}
}

func TestStatMissing(t *testing.T) {
	fsys := testFS(t, map[string]fsEntry{"/tmp": dirEntry("/tmp")}, "/")
	for _, p := range []string{"/nope", "/tmp/nope", "/nope/deeper"} {
		if _, err := fsys.Stat(p); !errors.Is(err, fs.ErrNotExist) {
			t.Errorf("Stat(%q) err = %v, want fs.ErrNotExist", p, err)
		}
	}
}
