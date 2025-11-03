package container

import (
	"encoding/json"
	"errors"
	"fmt"
	"log/slog"
	"os"
	"path/filepath"
	"strings"
)

// ProcessSpec mirrors the crun --process JSON structure
type ProcessSpec struct {
	Terminal bool     `json:"terminal"`
	Args     []string `json:"args"`
	Env      []string `json:"env"`
	Cwd      string   `json:"cwd"`
}

var (
	processTemplate *ProcessSpec
)

// InitProcessTemplateFromEnv loads the process template from $SPRITE_WRITE_DIR/tmp/process.json
// This is best-effort and may race with writers; callers should tolerate nil and retry lazily.
func InitProcessTemplateFromEnv() {
	writeDir := os.Getenv("SPRITE_WRITE_DIR")
	if writeDir == "" {
		slog.Warn("InitProcessTemplateFromEnv: SPRITE_WRITE_DIR is unset; process template not loaded")
		return
	}
	path := filepath.Join(writeDir, "tmp", "process.json")
	data, err := os.ReadFile(path)
	if err != nil {
		if os.IsNotExist(err) {
			slog.Warn("InitProcessTemplateFromEnv: process.json not found", "path", path)
		} else {
			slog.Error("InitProcessTemplateFromEnv: failed to read process.json", "error", err, "path", path)
		}
		return
	}
	var tmpl ProcessSpec
	if err := json.Unmarshal(data, &tmpl); err != nil {
		slog.Error("InitProcessTemplateFromEnv: invalid process.json", "error", err, "path", path)
		return
	}
	processTemplate = &tmpl
}

// HasProcessTemplate reports whether a template is loaded
func HasProcessTemplate() bool {
	return processTemplate != nil
}

// CloneProcessTemplate returns a deep copy of the loaded template. If the template
// hasn't been loaded yet, this will attempt to load it from the environment on demand.
func CloneProcessTemplate() (*ProcessSpec, error) {
	// Lazy-init on demand
	if processTemplate == nil {
		InitProcessTemplateFromEnv()
	}
	src := processTemplate
	if src == nil {
		return nil, errors.New("process template not loaded")
	}
	dst := &ProcessSpec{
		Terminal: src.Terminal,
		Cwd:      src.Cwd,
	}
	if len(src.Args) > 0 {
		dst.Args = append([]string(nil), src.Args...)
	}
	if len(src.Env) > 0 {
		dst.Env = append([]string(nil), src.Env...)
	}
	return dst, nil
}

// mergeEnv overrides keys from base with overrides; keys are NAME=VALUE strings
func mergeEnv(base, overrides []string) []string {
	if len(overrides) == 0 {
		return append([]string(nil), base...)
	}
	// Build map from base
	result := make(map[string]string, len(base))
	order := make([]string, 0, len(base))
	for _, kv := range base {
		if i := strings.IndexByte(kv, '='); i > 0 {
			key := kv[:i]
			val := kv[i+1:]
			result[key] = val
			order = append(order, key)
		}
	}
	// Apply overrides (preserve new keys order after base)
	var newKeys []string
	for _, kv := range overrides {
		if i := strings.IndexByte(kv, '='); i > 0 {
			key := kv[:i]
			val := kv[i+1:]
			if _, ok := result[key]; !ok {
				newKeys = append(newKeys, key)
			}
			result[key] = val
		}
	}
	// Rebuild slice preserving base order then new keys in arrival order
	out := make([]string, 0, len(result))
	for _, k := range order {
		out = append(out, k+"="+result[k])
	}
	for _, k := range newKeys {
		out = append(out, k+"="+result[k])
	}
	return out
}

// writeProcessJSON writes the given spec to a unique file and returns its path
func writeProcessJSON(spec *ProcessSpec) (string, error) {
	dir := "/.sprite/tmp/.crun"
	if err := os.MkdirAll(dir, 0755); err != nil {
		return "", fmt.Errorf("failed to create process dir: %w", err)
	}
	// Use pid+rand-ish suffix based on timestamp counter to avoid collisions
	fname := fmt.Sprintf("process-%d-%d.json", os.Getpid(), os.Getuid())
	// If exists, append a monotonic counter
	path := filepath.Join(dir, fname)
	// Best-effort uniqueness: try up to a few different names
	for i := 0; i < 5; i++ {
		if i > 0 {
			path = filepath.Join(dir, fmt.Sprintf("process-%d-%d-%d.json", os.Getpid(), os.Getuid(), i))
		}
		if _, err := os.Stat(path); err != nil {
			data, mErr := json.Marshal(spec)
			if mErr != nil {
				return "", mErr
			}
			if wErr := os.WriteFile(path, data, 0644); wErr != nil {
				return "", wErr
			}
			return path, nil
		}
	}
	return "", errors.New("failed to allocate unique process.json path")
}
