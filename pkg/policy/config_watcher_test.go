package policy

import (
	"os"
	"path/filepath"
	"testing"
)

func TestMatchesPattern(t *testing.T) {
	tests := []struct {
		domain  string
		pattern string
		want    bool
	}{
		// Exact matches
		{"example.com", "example.com", true},
		{"example.com", "other.com", false},

		// Wildcard *
		{"anything.com", "*", true},
		{"example.com", "*", true},

		// Subdomain wildcard
		{"a.example.com", "*.example.com", true},
		{"b.a.example.com", "*.example.com", true},
		{"example.com", "*.example.com", true}, // base domain should also match
		{"notexample.com", "*.example.com", false},
		{"anotherexample.com", "*.example.com", false},

		// Case insensitive
		{"Example.Com", "example.com", true},
		{"A.EXAMPLE.COM", "*.example.com", true},
	}

	for _, tt := range tests {
		got := MatchesPattern(tt.domain, tt.pattern)
		if got != tt.want {
			t.Errorf("MatchesPattern(%q, %q) = %v, want %v", tt.domain, tt.pattern, got, tt.want)
		}
	}
}

func TestLoadNetworkConfig(t *testing.T) {
	// Create temp directory for test configs
	tmpDir := t.TempDir()

	tests := []struct {
		name       string
		configJSON string
		wantMode   PolicyMode
		wantRules  int
		wantErr    bool
	}{
		{
			name:       "empty rules - unrestricted",
			configJSON: `{"rules": []}`,
			wantMode:   Unrestricted,
			wantRules:  0,
			wantErr:    false,
		},
		{
			name:       "no file - unrestricted",
			configJSON: "",
			wantMode:   Unrestricted,
			wantRules:  0,
			wantErr:    true,
		},
		{
			name: "simple domain rules",
			configJSON: `{
				"rules": [
					{"domain": "example.com", "action": "allow"},
					{"domain": "test.com", "action": "deny"}
				]
			}`,
			wantMode:  DefaultRestricted,
			wantRules: 2,
			wantErr:   false,
		},
		{
			name: "include defaults",
			configJSON: `{
				"rules": [
					{"include": "defaults"}
				]
			}`,
			wantMode:  DefaultRestricted,
			wantRules: len(DefaultAllowedDomains()),
			wantErr:   false,
		},
		{
			name: "include defaults with custom",
			configJSON: `{
				"rules": [
					{"include": "defaults"},
					{"domain": "custom.com", "action": "allow"}
				]
			}`,
			wantMode:  DefaultRestricted,
			wantRules: len(DefaultAllowedDomains()) + 1,
			wantErr:   false,
		},
		{
			name: "include with action override",
			configJSON: `{
				"rules": [
					{"include": "defaults", "action": "deny"}
				]
			}`,
			wantMode:  DefaultRestricted,
			wantRules: len(DefaultAllowedDomains()),
			wantErr:   false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			testDir := filepath.Join(tmpDir, tt.name)
			if err := os.MkdirAll(testDir, 0755); err != nil {
				t.Fatalf("failed to create test dir: %v", err)
			}

			if tt.configJSON != "" {
				configPath := filepath.Join(testDir, "network.json")
				if err := os.WriteFile(configPath, []byte(tt.configJSON), 0644); err != nil {
					t.Fatalf("failed to write config: %v", err)
				}
			}

			mode, rules, err := LoadNetworkConfig(testDir)
			if (err != nil) != tt.wantErr {
				t.Errorf("LoadNetworkConfig() error = %v, wantErr %v", err, tt.wantErr)
				return
			}

			if !tt.wantErr {
				if mode != tt.wantMode {
					t.Errorf("LoadNetworkConfig() mode = %v, want %v", mode, tt.wantMode)
				}
				if len(rules) != tt.wantRules {
					t.Errorf("LoadNetworkConfig() rules count = %d, want %d", len(rules), tt.wantRules)
				}
			}
		})
	}
}

func TestRuleEvaluation(t *testing.T) {
	tests := []struct {
		name    string
		rules   []Rule
		domain  string
		want    bool
		comment string
	}{
		{
			name:    "empty rules allow (unrestricted)",
			rules:   []Rule{},
			domain:  "example.com",
			want:    true,
			comment: "no rules means unrestricted - allow everything",
		},
		{
			name: "exact match allow",
			rules: []Rule{
				{Domain: "example.com", Action: "allow"},
			},
			domain: "example.com",
			want:   true,
		},
		{
			name: "exact match deny",
			rules: []Rule{
				{Domain: "example.com", Action: "deny"},
			},
			domain: "example.com",
			want:   false,
		},
		{
			name: "wildcard allow all",
			rules: []Rule{
				{Domain: "*", Action: "allow"},
			},
			domain: "anything.com",
			want:   true,
		},
		{
			name: "allow all then deny specific",
			rules: []Rule{
				{Domain: "*", Action: "allow"},
				{Domain: "blocked.com", Action: "deny"},
			},
			domain:  "blocked.com",
			want:    false,
			comment: "exact match is more specific than wildcard",
		},
		{
			name: "deny specific with allow all (order doesn't matter)",
			rules: []Rule{
				{Domain: "blocked.com", Action: "deny"},
				{Domain: "*", Action: "allow"},
			},
			domain:  "blocked.com",
			want:    false,
			comment: "exact match is more specific than wildcard",
		},
		{
			name: "allow all then deny specific - other domain",
			rules: []Rule{
				{Domain: "*", Action: "allow"},
				{Domain: "blocked.com", Action: "deny"},
			},
			domain:  "allowed.com",
			want:    true,
			comment: "wildcard matches when no more specific rule exists",
		},
		{
			name: "subdomain wildcard",
			rules: []Rule{
				{Domain: "*.example.com", Action: "allow"},
			},
			domain: "sub.example.com",
			want:   true,
		},
		{
			name: "nested subdomain wildcard",
			rules: []Rule{
				{Domain: "*.example.com", Action: "allow"},
			},
			domain: "a.b.example.com",
			want:   true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Create a DNS server with the test rules
			server := &DNSServer{
				rules: tt.rules,
			}

			got := server.isAllowed(tt.domain)
			if got != tt.want {
				t.Errorf("isAllowed(%q) = %v, want %v (%s)", tt.domain, got, tt.want, tt.comment)
			}
		})
	}
}

