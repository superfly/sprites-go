package sprites

import "testing"

func TestExtractChannel(t *testing.T) {
	tests := []struct {
		version string
		want    string
	}{
		{"v0.0.1", "release"},
		{"0.0.1", "release"},
		{"v1.0.0", "release"},
		{"v0.0.1-rc1", "rc"},
		{"v0.0.1-rc29", "rc"},
		{"v0.0.1-rc30", "rc"},
		{"0.0.1-rc99", "rc"},
		{"v0.0.1-dev", "dev"},
		{"v0.0.1-dev-abc1234", "dev"},
		{"0.1.2-dev-abc1234", "dev"},
		{"v0.0.1-beta1", "beta"},
	}

	for _, tt := range tests {
		t.Run(tt.version, func(t *testing.T) {
			got := extractChannel(tt.version)
			if got != tt.want {
				t.Errorf("extractChannel(%q) = %q, want %q", tt.version, got, tt.want)
			}
		})
	}
}

func TestSupportsPathAttach(t *testing.T) {
	tests := []struct {
		version string
		want    bool
	}{
		// Unknown version - use legacy
		{"", false},

		// Dev versions - always support path attach
		{"v0.0.1-dev", true},
		{"v0.0.1-dev-abc123", true},
		{"0.0.1-dev-xyz789", true},

		// RC versions - only rc30+ support path attach
		{"v0.0.1-rc1", false},
		{"v0.0.1-rc28", false},
		{"v0.0.1-rc29", false},
		{"v0.0.1-rc30", true},
		{"v0.0.1-rc31", true},
		{"v0.0.1-rc99", true},

		// Release versions - support path attach
		{"v0.0.1", true},
		{"v0.1.0", true},
		{"v1.0.0", true},
		{"1.0.0", true},

		// Invalid versions - use legacy
		{"invalid", false},
		{"not-a-version", false},
	}

	for _, tt := range tests {
		t.Run(tt.version, func(t *testing.T) {
			got := supportsPathAttach(tt.version)
			if got != tt.want {
				t.Errorf("supportsPathAttach(%q) = %v, want %v", tt.version, got, tt.want)
			}
		})
	}
}
