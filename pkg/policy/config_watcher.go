package policy

import (
	"context"
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/fsnotify/fsnotify"
)

type networkJSON struct {
	Mode    string             `json:"mode"`
	Domains []networkJSONEntry `json:"domains"`
}
type networkJSONEntry struct {
	Domain string `json:"domain"`
	Action string `json:"action"` // allow|block (block ignored for now)
}

// LoadNetworkConfig reads network.json from dir and returns PolicyMode and allowlist.
func LoadNetworkConfig(dir string) (PolicyMode, []string, error) {
	path := filepath.Join(strings.TrimSpace(dir), "network.json")
	data, err := os.ReadFile(path)
	if err != nil {
		return Unrestricted, nil, err
	}
	var cfg networkJSON
	if err := json.Unmarshal(data, &cfg); err != nil {
		return Unrestricted, nil, err
	}
	mode := strings.ToLower(strings.TrimSpace(cfg.Mode))
	pm := Unrestricted
	switch mode {
	case "unrestricted":
		pm = Unrestricted
	case "defaults":
		pm = DefaultRestricted
	case "custom":
		pm = DefaultRestricted
	case "custom_plus_defaults":
		pm = DefaultRestricted
	default:
		pm = Unrestricted
	}
	var allow []string
	if mode == "defaults" || mode == "custom_plus_defaults" {
		allow = append(allow, DefaultAllowedDomains()...)
	}
	if mode == "custom" || mode == "custom_plus_defaults" {
		for _, e := range cfg.Domains {
			if strings.ToLower(e.Action) != "allow" {
				continue
			}
			d := strings.TrimSpace(e.Domain)
			if d != "" {
				allow = append(allow, d)
			}
		}
	}
	return pm, allow, nil
}

// WatchNetworkConfig watches dir for changes to network.json and calls onChange after a short debounce.
func WatchNetworkConfig(ctx context.Context, dir string, onChange func()) (*fsnotify.Watcher, error) {
	w, err := fsnotify.NewWatcher()
	if err != nil {
		return nil, err
	}
	if err := w.Add(dir); err != nil {
		_ = w.Close()
		return nil, err
	}
	target := filepath.Base(filepath.Join(dir, "network.json"))
	var timer *time.Timer
	debounce := func() {
		if timer != nil {
			timer.Stop()
		}
		timer = time.AfterFunc(200*time.Millisecond, func() { onChange() })
	}
	go func() {
		defer w.Close()
		for {
			select {
			case <-ctx.Done():
				return
			case ev, ok := <-w.Events:
				if !ok {
					return
				}
				if filepath.Base(ev.Name) != target {
					continue
				}
				if ev.Op&(fsnotify.Write|fsnotify.Create|fsnotify.Rename) != 0 {
					debounce()
				}
			case <-w.Errors:
				// ignore
			}
		}
	}()
	return w, nil
}
