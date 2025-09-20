package v1

// Config represents the sprite configuration for version 1
type Config struct {
	Version          string                `json:"version"`
	CurrentSelection *CurrentSelection     `json:"current_selection,omitempty"`
	URLs             map[string]*URLConfig `json:"urls"`                  // key: API URL
	URLAliases       map[string]string     `json:"url_aliases,omitempty"` // key: alias, value: URL
	DisableKeyring   bool                  `json:"disable_keyring,omitempty"`
	LastVersionCheck string                `json:"last_version_check,omitempty"`
	LatestVersion    string                `json:"latest_version,omitempty"`
	CurrentVersion   string                `json:"current_version,omitempty"`
}

// CurrentSelection tracks the currently selected organization
type CurrentSelection struct {
	URL string `json:"url"`
	Org string `json:"org"`
}

// URLConfig represents configuration for a specific API URL
type URLConfig struct {
	URL  string                `json:"url"`
	Orgs map[string]*OrgConfig `json:"orgs"` // key: org name
}

// OrgConfig represents configuration for a specific organization
type OrgConfig struct {
	Name        string                   `json:"name"`
	KeychainKey string                   `json:"keychain_key"`          // The key used to store token in keychain
	Token       string                   `json:"token,omitempty"`       // Only used when keyring is disabled
	UseKeyring  bool                     `json:"use_keyring,omitempty"` // Tracks whether keyring is being used
	Sprites     map[string]*SpriteConfig `json:"sprites"`               // key: sprite name
}

// SpriteConfig represents configuration for a specific sprite
type SpriteConfig struct {
	Name string `json:"name"`
}
