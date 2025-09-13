package main

import (
	"fmt"
	"os"
	"strings"
	"time"

	"github.com/superfly/sprite-env/client/commands"
	"github.com/superfly/sprite-env/client/config"
	"golang.org/x/term"
)

// updateInfo contains information about available updates
type updateInfo struct {
	currentVersion  string
	latestVersion   string
	forceShow       bool              // Show version info even if no update available
	cmdPath         string            // The command invocation path
	detailedInfo    bool              // Show detailed version discovery info
	channelVersions map[string]string // Versions found in each channel
	currentChannel  string            // Current channel name
}

// CheckForUpdatesAsync checks for updates in the background and returns a channel with the result
func CheckForUpdatesAsync(cfg *config.Manager, currentVersion string, cmdPath string) <-chan *updateInfo {
	resultChan := make(chan *updateInfo, 1)

	// Don't check if we've checked recently (within 24 hours)
	if !shouldCheckVersion(cfg) {
		close(resultChan)
		return resultChan
	}

	go func() {
		defer close(resultChan)

		// Check for updates
		result, err := commands.GetLatestVersionForChannelDetailed(currentVersion)
		if err != nil {
			// If debug is enabled, show the error
			if os.Getenv("SPRITE_VERSION_DEBUG") == "true" {
				resultChan <- &updateInfo{
					currentVersion:  currentVersion,
					latestVersion:   "error: " + err.Error(),
					detailedInfo:    true,
					currentChannel:  commands.ExtractChannel(currentVersion),
					channelVersions: make(map[string]string),
				}
			}
			return
		}

		// Update last check time
		cfg.SetLastVersionCheck(time.Now().Format(time.RFC3339))
		cfg.SetLatestVersion(result.LatestVersion)
		cfg.Save() // Ignore error - this is background

		// Check if we should show version info
		detailedInfo := os.Getenv("SPRITE_VERSION_DEBUG") == "true"
		showUpdate := shouldShowUpdateMessage(currentVersion, result.LatestVersion)

		// Send result if update is available or if detailed info requested
		if showUpdate || detailedInfo {
			resultChan <- &updateInfo{
				currentVersion:  currentVersion,
				latestVersion:   result.LatestVersion,
				forceShow:       false,
				cmdPath:         cmdPath,
				detailedInfo:    detailedInfo,
				channelVersions: result.ChannelVersions,
				currentChannel:  result.CurrentChannel,
			}
		}
	}()

	return resultChan
}

// PrintUpdateMessage waits for the update check result and prints a message if needed
func PrintUpdateMessage(updateChan <-chan *updateInfo) {
	// Only print update messages if stderr is a terminal
	if !term.IsTerminal(int(os.Stderr.Fd())) {
		return
	}

	// Check if terminal supports colors
	supportsColor := os.Getenv("TERM") != "dumb" && os.Getenv("NO_COLOR") == ""

	// This runs as a defer, so it's the last thing before exit
	select {
	case info := <-updateChan:
		if info != nil {
			fmt.Fprintf(os.Stderr, "\n")
			if info.detailedInfo {
				// Show detailed version discovery information
				fmt.Fprintf(os.Stderr, "Version check debug:\n")
				fmt.Fprintf(os.Stderr, "  Current: %s (channel: %s)\n", info.currentVersion, info.currentChannel)
				if len(info.channelVersions) > 0 {
					fmt.Fprintf(os.Stderr, "  Found:\n")
					for channel, version := range info.channelVersions {
						if version != "" {
							fmt.Fprintf(os.Stderr, "    %s: %s\n", channel, version)
						}
					}
				}
				fmt.Fprintf(os.Stderr, "  Selected: %s\n", info.latestVersion)

				// Show appropriate action
				if !strings.HasPrefix(info.latestVersion, "error:") {
					normalizedCurrent := strings.TrimPrefix(info.currentVersion, "v")
					normalizedLatest := strings.TrimPrefix(info.latestVersion, "v")
					if normalizedCurrent != normalizedLatest && !strings.HasSuffix(info.currentVersion, "-dev") {
						if supportsColor {
							fmt.Fprintf(os.Stderr, "\n\033[33mUpgrade available\033[0m (%s → %s)\n", info.currentVersion, info.latestVersion)
							fmt.Fprintf(os.Stderr, "Run '\033[36m%s upgrade\033[0m' to update\n", info.cmdPath)
						} else {
							fmt.Fprintf(os.Stderr, "\nUpgrade available (%s → %s)\n", info.currentVersion, info.latestVersion)
							fmt.Fprintf(os.Stderr, "Run '%s upgrade' to update\n", info.cmdPath)
						}
					} else if strings.HasSuffix(info.currentVersion, "-dev") {
						fmt.Fprintf(os.Stderr, "\nRunning development version\n")
						fmt.Fprintf(os.Stderr, "Run '%s upgrade' to install release version\n", info.cmdPath)
					} else {
						if supportsColor {
							fmt.Fprintf(os.Stderr, "\n\033[32mUp to date\033[0m\n")
						} else {
							fmt.Fprintf(os.Stderr, "\nUp to date\n")
						}
					}
				}
			} else {
				// Update is available - show simple colored notification
				if supportsColor {
					fmt.Fprintf(os.Stderr, "\033[33mUpgrade available\033[0m (%s → %s)\n", info.currentVersion, info.latestVersion)
					fmt.Fprintf(os.Stderr, "Run '\033[36m%s upgrade\033[0m' to update\n", info.cmdPath)
				} else {
					fmt.Fprintf(os.Stderr, "Upgrade available (%s → %s)\n", info.currentVersion, info.latestVersion)
					fmt.Fprintf(os.Stderr, "Run '%s upgrade' to update\n", info.cmdPath)
				}
			}
			fmt.Fprintf(os.Stderr, "\n")
		}
	case <-time.After(3 * time.Second):
		// Wait up to 3 seconds for the check to complete
	}
}

func shouldCheckVersion(cfg *config.Manager) bool {
	// Force check if UPGRADE_CHECK=true or SPRITE_VERSION_DEBUG=true
	if os.Getenv("UPGRADE_CHECK") == "true" || os.Getenv("SPRITE_VERSION_DEBUG") == "true" {
		return true
	}

	lastCheck := cfg.GetLastVersionCheck()
	if lastCheck == "" {
		return true
	}

	last, err := time.Parse(time.RFC3339, lastCheck)
	if err != nil {
		return true
	}

	// Check if 24 hours have passed
	return time.Since(last) > 24*time.Hour
}

func shouldShowUpdateMessage(currentVersion, latestVersion string) bool {
	if currentVersion == "" || latestVersion == "" {
		return false
	}

	// Don't show update message for dev versions
	if strings.HasSuffix(currentVersion, "-dev") {
		return false
	}

	// Normalize versions for comparison (remove v prefix)
	normalizedCurrent := strings.TrimPrefix(currentVersion, "v")
	normalizedLatest := strings.TrimPrefix(latestVersion, "v")

	// Don't show if already on latest
	if normalizedCurrent == normalizedLatest {
		return false
	}

	return true
}
