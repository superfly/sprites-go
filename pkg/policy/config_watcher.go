package policy

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/fsnotify/fsnotify"
)

type networkJSON struct {
	Rules []networkJSONRule `json:"rules"`
}

type networkJSONRule struct {
	// Domain rule fields
	Domain string `json:"domain,omitempty"`
	Action string `json:"action,omitempty"` // allow|deny

	// Include rule fields
	Include string `json:"include,omitempty"` // e.g., "defaults"
	// Action can also be used with Include to override all included actions
}

// Rule represents a network policy rule after expansion.
type Rule struct {
	Domain string // Domain pattern (supports wildcards)
	Action string // "allow" or "deny"
}

// LoadNetworkConfig reads network.json from dir and returns PolicyMode and rule list.
func LoadNetworkConfig(dir string) (PolicyMode, []Rule, error) {
	path := filepath.Join(strings.TrimSpace(dir), "network.json")
	data, err := os.ReadFile(path)
	if err != nil {
		return Unrestricted, nil, err
	}
	var cfg networkJSON
	if err := json.Unmarshal(data, &cfg); err != nil {
		return Unrestricted, nil, err
	}

	// If no rules, return unrestricted mode
	if len(cfg.Rules) == 0 {
		return Unrestricted, nil, nil
	}

	// Expand rules (process includes)
	var rules []Rule
	for _, r := range cfg.Rules {
		if r.Include != "" {
			// Handle include rule
			includedRules, err := expandInclude(r.Include, r.Action)
			if err != nil {
				// Skip invalid includes
				continue
			}
			rules = append(rules, includedRules...)
		} else if r.Domain != "" {
			// Handle domain rule
			action := strings.ToLower(strings.TrimSpace(r.Action))
			if action != "allow" && action != "deny" {
				// Skip invalid actions
				continue
			}
			rules = append(rules, Rule{
				Domain: strings.ToLower(strings.TrimSpace(r.Domain)),
				Action: action,
			})
		}
	}

	// If we have any rules, use restricted mode
	if len(rules) > 0 {
		return DefaultRestricted, rules, nil
	}

	return Unrestricted, nil, nil
}

// expandInclude expands an include rule by injecting domains from the named set.
func expandInclude(name string, actionOverride string) ([]Rule, error) {
	name = strings.ToLower(strings.TrimSpace(name))
	actionOverride = strings.ToLower(strings.TrimSpace(actionOverride))

	// Validate action override if provided
	if actionOverride != "" && actionOverride != "allow" && actionOverride != "deny" {
		return nil, fmt.Errorf("invalid action override: %s", actionOverride)
	}

	var rules []Rule
	switch name {
	case "defaults":
		domains := DefaultAllowedDomains()
		action := "allow" // natural action for defaults
		if actionOverride != "" {
			action = actionOverride
		}
		for _, domain := range domains {
			rules = append(rules, Rule{
				Domain: strings.ToLower(domain),
				Action: action,
			})
		}
	default:
		return nil, fmt.Errorf("unknown include set: %s", name)
	}

	return rules, nil
}

// MatchesPattern checks if a domain matches a pattern with wildcard support.
// - "*" matches any domain
// - "*.example.com" matches any subdomain of example.com (including nested like a.b.example.com)
// - "example.com" matches exactly "example.com"
func MatchesPattern(domain, pattern string) bool {
	domain = strings.ToLower(strings.TrimSpace(domain))
	pattern = strings.ToLower(strings.TrimSpace(pattern))

	// Wildcard "*" matches everything
	if pattern == "*" {
		return true
	}

	// Exact match
	if domain == pattern {
		return true
	}

	// Wildcard subdomain pattern: "*.example.com"
	if strings.HasPrefix(pattern, "*.") {
		suffix := pattern[2:] // Remove "*."
		// Check if domain ends with .suffix (e.g., "a.example.com" ends with ".example.com")
		if strings.HasSuffix(domain, "."+suffix) {
			return true
		}
		// Also match the base domain itself if it matches
		if domain == suffix {
			return true
		}
	}

	return false
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
				if ev.Op&(fsnotify.Write|fsnotify.Create|fsnotify.Rename|fsnotify.Remove) != 0 {
					debounce()
				}
			case <-w.Errors:
				// ignore
			}
		}
	}()
	return w, nil
}
