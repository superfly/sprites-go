package v0

// Config represents the sprite configuration for version 0 (legacy)
type Config struct {
	CurrentOrg       string                   `json:"current_org,omitempty"`
	Orgs             map[string]*Organization `json:"orgs"`
	DisableKeyring   bool                     `json:"disable_keyring,omitempty"`
	LastVersionCheck string                   `json:"last_version_check,omitempty"`
	LatestVersion    string                   `json:"latest_version,omitempty"`
	CurrentVersion   string                   `json:"current_version,omitempty"`
}

// Organization represents an organization configuration for version 0
type Organization struct {
	Name       string `json:"name"`
	Token      string `json:"token,omitempty"` // Only used when keyring is disabled
	URL        string `json:"url"`
	UseKeyring bool   `json:"use_keyring,omitempty"` // Tracks whether keyring is being used for this org
}
