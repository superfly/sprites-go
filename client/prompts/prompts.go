package prompts

import (
	"bufio"
	"fmt"
	"os"
	"strings"
	"time"

	"github.com/sprite-env/client/config"
	"github.com/sprite-env/client/format"
	"golang.org/x/term"
)

// PromptForInitialLogin prompts the user to login when no organizations are configured
func PromptForInitialLogin(cfg *config.Manager) (*config.Organization, error) {
	fmt.Println("We need an API token to work with Sprites:")
	fmt.Print("Enter your API token: ")
	
	// Get token input
	var token string
	if term.IsTerminal(int(os.Stdin.Fd())) {
		tokenBytes, err := term.ReadPassword(int(os.Stdin.Fd()))
		fmt.Println() // New line after password
		if err != nil {
			return nil, fmt.Errorf("failed to read token: %w", err)
		}
		token = string(tokenBytes)
	} else {
		token = readLine()
	}
	
	if token == "" {
		return nil, fmt.Errorf("API token is required")
	}
	
	// Generate a simple org name based on timestamp
	orgName := fmt.Sprintf("default-%d", time.Now().Unix())
	
	// Use the Sprites API URL (can be overridden with SPRITES_API_URL)
	url := "https://api.sprites.dev"
	if envURL := os.Getenv("SPRITES_API_URL"); envURL != "" {
		url = envURL
	}
	
	// Add the organization
	if err := cfg.AddOrg(orgName, token, url); err != nil {
		return nil, fmt.Errorf("failed to save credentials: %w", err)
	}
	
	fmt.Println("\n" + format.Success("✓ Ready to work with Sprites!") + "\n")
	
	// Return the newly added org
	return cfg.GetOrgs()[orgName], nil
}

// getOrgDisplayName returns a user-friendly display name for the organization
func getOrgDisplayName(org *config.Organization) string {
	return format.GetOrgDisplayName(org.Name, org.URL)
}

// SelectOrganization prompts the user to select an organization
func SelectOrganization(cfg *config.Manager) (*config.Organization, error) {
	orgs := cfg.GetOrgs()
	
	if len(orgs) == 0 {
		return nil, fmt.Errorf("no organizations configured. Please run 'sprite org auth' first")
	}
	
	if len(orgs) == 1 {
		// Only one org, use it automatically
		for _, org := range orgs {
			return org, nil
		}
	}

	// Check if terminal supports interactive mode
	if !term.IsTerminal(int(os.Stdin.Fd())) {
		return nil, fmt.Errorf("interactive mode not available. Please set current org with environment variable")
	}

	// Create a sorted list of org names
	var orgNames []string
	for name := range orgs {
		orgNames = append(orgNames, name)
	}

	fmt.Println("Select an organization:")
	selected := selectFromList(orgNames)
	
	if selected == "" {
		return nil, fmt.Errorf("no organization selected")
	}

	// Set as current org
	if err := cfg.SetCurrentOrg(selected); err != nil {
		return nil, err
	}

	return orgs[selected], nil
}

// SelectOrCreateSprite prompts the user to select or create a sprite
func SelectOrCreateSprite(cfg *config.Manager, org *config.Organization) (*config.Sprite, bool, error) {
	// Sync sprites from API if using the new API
	if strings.Contains(org.URL, "sprites.dev") {
		fmt.Print("Fetching sprites...")
		// Import the commands package to use SyncSpritesWithConfig
		// For now, we'll handle this differently to avoid circular dependencies
		sprites, err := fetchSpritesFromAPI(org)
		if err != nil {
			fmt.Printf("\rWarning: Failed to fetch sprites from API: %v\n", err)
			// Continue with local config
		} else {
			fmt.Printf("\r\033[K") // Clear the line
			// Update org's sprites
			if org.Sprites == nil {
				org.Sprites = make(map[string]*config.Sprite)
			}
			// Clear and repopulate
			for k := range org.Sprites {
				delete(org.Sprites, k)
			}
			for _, sprite := range sprites {
				org.Sprites[sprite.Name] = &config.Sprite{
					Name: sprite.Name,
					ID:   sprite.ID,
				}
			}
		}
	}
	
	if org.Sprites == nil {
		org.Sprites = make(map[string]*config.Sprite)
	}

	sprites := org.Sprites
	
	// Check if terminal supports interactive mode
	if !term.IsTerminal(int(os.Stdin.Fd())) {
		return nil, false, fmt.Errorf("interactive mode not available")
	}

	if len(sprites) == 0 {
		// No sprites, prompt to create new one
		fmt.Println(format.Context(getOrgDisplayName(org), "Creating new Sprite, what would you like to call it?"))
		name := readLine()
		if name == "" {
			return nil, false, fmt.Errorf("no sprite name provided")
		}
		return &config.Sprite{Name: name}, true, nil
	}

	// Create options list
	options := []string{"[Create new sprite]"}
	var spriteNames []string
	for name := range sprites {
		spriteNames = append(spriteNames, name)
		options = append(options, name)
	}

	fmt.Println(format.Context(getOrgDisplayName(org), "Select a sprite:"))
	selected := selectFromList(options)
	
	if selected == "" {
		return nil, false, fmt.Errorf("no sprite selected")
	}

	if selected == "[Create new sprite]" {
		fmt.Println(format.Context(getOrgDisplayName(org), "Creating new Sprite, what would you like to call it?"))
		name := readLine()
		if name == "" {
			return nil, false, fmt.Errorf("no sprite name provided")
		}
		return &config.Sprite{Name: name}, true, nil
	}

	// Set as current sprite
	if err := cfg.SetCurrentSprite(selected); err != nil {
		return nil, false, err
	}

	return sprites[selected], false, nil
}

// selectFromList provides a simple text-based selection menu
func selectFromList(items []string) string {
	if len(items) == 0 {
		return ""
	}

	// For now, use a simple numbered list
	// TODO: Add arrow key navigation when we add a proper TUI library
	for i, item := range items {
		fmt.Printf("  %d. %s\n", i+1, item)
	}
	
	fmt.Print("Enter number (1-", len(items), "): ")
	reader := bufio.NewReader(os.Stdin)
	input, err := reader.ReadString('\n')
	if err != nil {
		return ""
	}
	
	input = strings.TrimSpace(input)
	var choice int
	if _, err := fmt.Sscanf(input, "%d", &choice); err != nil {
		return ""
	}
	
	if choice < 1 || choice > len(items) {
		return ""
	}
	
	return items[choice-1]
}

// readLine reads a line from stdin
func readLine() string {
	reader := bufio.NewReader(os.Stdin)
	input, err := reader.ReadString('\n')
	if err != nil {
		return ""
	}
	return strings.TrimSpace(input)
}

// PromptForAuth prompts for organization authentication details
func PromptForAuth() (name, url, token string, err error) {
	fmt.Println("Enter organization details:")
	
	fmt.Print("Organization name: ")
	name = readLine()
	if name == "" {
		return "", "", "", fmt.Errorf("organization name is required")
	}
	
	fmt.Print("API URL: ")
	url = readLine()
	if url == "" {
		return "", "", "", fmt.Errorf("API URL is required")
	}
	
	fmt.Print("API Token: ")
	// Try to hide password input
	if term.IsTerminal(int(os.Stdin.Fd())) {
		tokenBytes, err := term.ReadPassword(int(os.Stdin.Fd()))
		fmt.Println() // New line after password
		if err != nil {
			return "", "", "", fmt.Errorf("failed to read token: %w", err)
		}
		token = string(tokenBytes)
	} else {
		token = readLine()
	}
	
	if token == "" {
		return "", "", "", fmt.Errorf("API token is required")
	}
	
	return name, url, token, nil
}