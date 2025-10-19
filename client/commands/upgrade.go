package commands

import (
	"archive/tar"
	"archive/zip"
	"compress/gzip"
	"encoding/json"
	"encoding/xml"
	"flag"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"os"
	"path/filepath"
	"regexp"
	"runtime"
	"strings"
	"time"

	"github.com/superfly/sprite-env/client/config"
	"github.com/superfly/sprite-env/client/prompts"

	"github.com/Masterminds/semver/v3"
)

// S3Object represents a single object in the S3 bucket
type S3Object struct {
	Key          string    `json:"Key" xml:"Key"`
	LastModified time.Time `json:"LastModified" xml:"LastModified"`
	Size         int64     `json:"Size" xml:"Size"`
	ETag         string    `xml:"ETag"`
	StorageClass string    `xml:"StorageClass"`
}

// S3ListResult represents the result of listing objects in the S3 bucket
type S3ListResult struct {
	Contents []S3Object `json:"Contents" xml:"Contents"`
	Name     string     `xml:"Name"`
	Prefix   string     `xml:"Prefix"`
	MaxKeys  int        `xml:"MaxKeys"`
}

// UpgradeCommand handles the upgrade functionality
func UpgradeCommand(globalCtx *GlobalContext, args []string) {
	cmd := &Command{
		Name:        "upgrade",
		Usage:       "upgrade [options]",
		Description: "Upgrade the sprite client to the latest version",
		FlagSet:     flag.NewFlagSet("upgrade", flag.ExitOnError),
		Examples: []string{
			"sprite upgrade                  # Upgrade to the latest version",
			"sprite upgrade --check          # Check for available updates",
			"sprite upgrade --force          # Force upgrade even if up to date",
		},
	}

	var checkOnly bool
	var force bool
	var version string

	flags := NewGlobalFlags(cmd.FlagSet)
	_ = flags
	cmd.FlagSet.BoolVar(&checkOnly, "check", false, "Check for updates without installing")
	cmd.FlagSet.BoolVar(&force, "force", false, "Force upgrade even if already up to date")
	cmd.FlagSet.StringVar(&version, "version", "", "Upgrade to a specific version")

	_, err := ParseFlags(cmd, args)
	if err != nil {
		os.Exit(1)
	}

	if err := runUpgrade(globalCtx, checkOnly, force, version); err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}
}

func runUpgrade(globalCtx *GlobalContext, checkOnly, force bool, targetVersion string) error {
	cfg := globalCtx.ConfigMgr
	bucketURL := "https://sprites-binaries.t3.storage.dev/"
	clientPrefix := "client/"

	// Get the current executable path
	currentExe, err := os.Executable()
	if err != nil {
		return fmt.Errorf("failed to get current executable path: %w", err)
	}

	// Resolve any symlinks
	currentExe, err = filepath.EvalSymlinks(currentExe)
	if err != nil {
		return fmt.Errorf("failed to resolve executable path: %w", err)
	}

	// Skip the version check time limit for explicit upgrade commands
	// Only apply the time limit for automatic version checks (not implemented here)

	fmt.Println("Checking for updates...")
	slog.Debug("Starting upgrade check",
		"checkOnly", checkOnly,
		"force", force,
		"targetVersion", targetVersion,
		"currentExe", currentExe)

	// Find the latest version or the target version
	var selectedVersionStr string
	if targetVersion != "" {
		// Find specific version (supports partials) - need to list all versions
		slog.Debug("Listing bucket versions for specific version", "targetVersion", targetVersion)
		versions, err := listBucketVersions(bucketURL, clientPrefix)
		if err != nil {
			return fmt.Errorf("failed to list versions: %w", err)
		}

		if len(versions) == 0 {
			return fmt.Errorf("no versions found in the bucket")
		}

		// Normalize target (strip leading 'v')
		target := strings.TrimPrefix(targetVersion, "v")

		// Extract base and optional prerelease prefix from the target
		baseTarget := target
		prePrefix := ""
		if idx := strings.Index(target, "-"); idx != -1 {
			baseTarget = target[:idx]
			prePrefix = target[idx+1:]
		}

		var bestKey string
		var bestVer *semver.Version

		for vStr, v := range versions {
			// Split candidate into base and prerelease
			candBase := vStr
			candPre := ""
			if idx := strings.Index(vStr, "-"); idx != -1 {
				candBase = vStr[:idx]
				candPre = vStr[idx+1:]
			}

			// Match exact base (major.minor.patch)
			if candBase != baseTarget {
				continue
			}

			// If a prerelease prefix was provided, filter candidates
			if prePrefix != "" {
				// For dev, require exact '-dev' (no numeric suffixes)
				if prePrefix == "dev" {
					if candPre != "dev" {
						continue
					}
				} else {
					// For others (e.g., rc), allow prefix match like rc, rc1, rc2, etc.
					if candPre == "" || !strings.HasPrefix(candPre, prePrefix) {
						continue
					}
				}
			}

			if bestVer == nil || v.GreaterThan(bestVer) {
				bestVer = v
				bestKey = vStr
			}
		}

		if bestVer == nil {
			return fmt.Errorf("version %s not found", targetVersion)
		}

		// Keep 'v' prefix for bucket path consistency
		selectedVersionStr = "v" + bestKey
	} else {
		// Get the latest version using channel-based check (prefer binary version for channel detection)
		binaryVersion := globalCtx.Version
		currentVersion := binaryVersion
		if currentVersion == "" {
			currentVersion = cfg.GetCurrentVersion()
		}

		slog.Debug("Getting latest version for channel", "currentVersion", currentVersion)
		latestVersionStr, err := GetLatestVersionForChannel(currentVersion)
		if err != nil {
			return fmt.Errorf("failed to get latest version: %w", err)
		}
		slog.Debug("Latest version found", "version", latestVersionStr)

		selectedVersionStr = latestVersionStr
	}

	// Update last check time and latest version in config
	cfg.Load() // Reload config to ensure we have the latest
	cfg.SetLastVersionCheck(time.Now().Format(time.RFC3339))
	cfg.SetLatestVersion(selectedVersionStr)
	if err := cfg.Save(); err != nil {
		fmt.Fprintf(os.Stderr, "Warning: Failed to save version check time: %v\n", err)
	}

	fmt.Printf("Latest version: %s\n", selectedVersionStr)

	// Show current binary version (prefer embedded binary version)
	binaryVersion := globalCtx.Version
	if binaryVersion != "" {
		fmt.Printf("Current version: %s\n", binaryVersion)
	}

	// Determine if current binary is a dev build
	isDevVersion := ExtractChannel(binaryVersion) == "dev"

	if checkOnly {
		if binaryVersion != "" {
			if isDevVersion {
				fmt.Printf("You are running a development version (%s).\n", binaryVersion)
				// Always show the latest release version alongside dev builds
				releaseVersion, err := fetchVersionFromChannel("release")
				if err != nil || releaseVersion == "" {
					fmt.Printf("Latest available version: %s\n", selectedVersionStr)
				} else {
					fmt.Printf("Latest release version: %s\n", releaseVersion)
				}
			} else if strings.TrimPrefix(binaryVersion, "v") == strings.TrimPrefix(selectedVersionStr, "v") {
				fmt.Println("You are running the latest version.")
			} else {
				fmt.Println("An update is available. Run 'sprite upgrade' to install it.")
			}
		} else {
			fmt.Println("An update is available. Run 'sprite upgrade' to install it.")
		}
		return nil
	}

	// Check if we're already up to date
	if !force {
		if isDevVersion {
			// Dev versions are always considered newer than their base version
			normalizedCurrent := strings.TrimPrefix(binaryVersion, "v")
			baseVersion := normalizedCurrent
			if idx := strings.Index(normalizedCurrent, "-dev"); idx != -1 {
				baseVersion = normalizedCurrent[:idx]
			}
			normalizedSelected := strings.TrimPrefix(selectedVersionStr, "v")
			if strings.HasPrefix(normalizedSelected, baseVersion) && !strings.HasPrefix(normalizedSelected, baseVersion+"-dev") {
				fmt.Printf("You are running a development version (%s) which is newer than the latest release (%s).\n", binaryVersion, selectedVersionStr)
				fmt.Println("Use --force to downgrade to the release version.")
				return nil
			}

			// If we're on dev channel and targeting dev-latest, compare remote Last-Modified to local binary
			if selectedVersionStr == "dev-latest" {
				platform := getPlatform()
				var binaryName string
				if runtime.GOOS == "windows" {
					binaryName = fmt.Sprintf("sprite-%s.zip", platform)
				} else {
					binaryName = fmt.Sprintf("sprite-%s.tar.gz", platform)
				}
				downloadURL := fmt.Sprintf("%s%s%s/%s", bucketURL, clientPrefix, selectedVersionStr, binaryName)
				newer, err := isRemoteArchiveNewer(downloadURL, currentExe)
				if err == nil && !newer {
					fmt.Println("Already running the latest version.")
					return nil
				}
			}
		} else if binaryVersion == selectedVersionStr {
			// For dev builds, allow refresh if remote archive is newer than local binary timestamp
			if strings.Contains(selectedVersionStr, "-dev") {
				platform := getPlatform()
				var binaryName string
				if runtime.GOOS == "windows" {
					binaryName = fmt.Sprintf("sprite-%s.zip", platform)
				} else {
					binaryName = fmt.Sprintf("sprite-%s.tar.gz", platform)
				}
				downloadURL := fmt.Sprintf("%s%s%s/%s", bucketURL, clientPrefix, selectedVersionStr, binaryName)
				newer, err := isRemoteArchiveNewer(downloadURL, currentExe)
				if err == nil && !newer {
					fmt.Println("Already running the latest version.")
					return nil
				}
				// If remote is newer or we can't determine, continue to download
			} else {
				fmt.Println("Already running the latest version.")
				return nil
			}
		}
	}

	// Confirm before proceeding with the upgrade, unless forced
	if !force {
		desc := fmt.Sprintf("This will download and install %s, replacing the current binary at %s.", selectedVersionStr, currentExe)
		if targetVersion == "" {
			desc = fmt.Sprintf("This will upgrade to %s and replace the current binary at %s.", selectedVersionStr, currentExe)
		}
		confirmed, err := prompts.PromptForConfirmation("Upgrade sprite?", desc)
		if err != nil || !confirmed {
			fmt.Println("Upgrade cancelled.")
			return nil
		}
	}

	// Determine platform
	platform := getPlatform()
	var binaryName string
	if runtime.GOOS == "windows" {
		binaryName = fmt.Sprintf("sprite-%s.zip", platform)
	} else {
		binaryName = fmt.Sprintf("sprite-%s.tar.gz", platform)
	}
	downloadURL := fmt.Sprintf("%s%s%s/%s", bucketURL, clientPrefix, selectedVersionStr, binaryName)

	slog.Debug("Download URL constructed",
		"url", downloadURL,
		"platform", platform,
		"binaryName", binaryName)
	fmt.Printf("Downloading %s...\n", binaryName)

	// Create temporary directory
	tempDir, err := os.MkdirTemp("", "sprite-upgrade-*")
	if err != nil {
		return fmt.Errorf("failed to create temp directory: %w", err)
	}
	defer os.RemoveAll(tempDir)

	// Download the binary
	tempFile := filepath.Join(tempDir, binaryName)
	slog.Debug("Downloading file", "url", downloadURL, "destination", tempFile)
	if err := downloadFile(downloadURL, tempFile); err != nil {
		return fmt.Errorf("failed to download: %w", err)
	}
	slog.Debug("Download completed successfully")

	// Extract the binary
	extractedBinary := filepath.Join(tempDir, "sprite")
	if runtime.GOOS == "windows" {
		extractedBinary += ".exe"
	}

	// Extract based on file type
	if runtime.GOOS == "windows" {
		if err := extractZip(tempFile, tempDir); err != nil {
			return fmt.Errorf("failed to extract: %w", err)
		}
	} else {
		if err := extractTarGz(tempFile, tempDir); err != nil {
			return fmt.Errorf("failed to extract: %w", err)
		}
	}

	// Verify the extracted binary exists
	if _, err := os.Stat(extractedBinary); err != nil {
		return fmt.Errorf("extracted binary not found: %w", err)
	}

	// Make the new binary executable
	if runtime.GOOS != "windows" {
		if err := os.Chmod(extractedBinary, 0755); err != nil {
			return fmt.Errorf("failed to make binary executable: %w", err)
		}
	}

	// Replace the current binary
	fmt.Println("Installing new version...")
	slog.Debug("Replacing executable", "current", currentExe, "new", extractedBinary)
	if err := replaceExecutable(currentExe, extractedBinary); err != nil {
		return fmt.Errorf("failed to replace executable: %w", err)
	}
	slog.Debug("Executable replaced successfully")

	// Update current version in config
	cfg.SetCurrentVersion(selectedVersionStr)
	if err := cfg.Save(); err != nil {
		fmt.Fprintf(os.Stderr, "Warning: Failed to save current version: %v\n", err)
	}

	fmt.Printf("Successfully upgraded to version %s\n", selectedVersionStr)
	return nil
}

func shouldCheckVersion(cfg *config.Manager) bool {
	if cfg.GetLastVersionCheck() == "" {
		return true
	}

	lastCheck, err := time.Parse(time.RFC3339, cfg.GetLastVersionCheck())
	if err != nil {
		return true
	}

	// Check once every 24 hours
	return time.Since(lastCheck) > 24*time.Hour
}

// VersionCheckResult contains detailed version check information
type VersionCheckResult struct {
	LatestVersion   string
	CurrentChannel  string
	ChannelVersions map[string]string
}

// GetLatestVersionForChannel gets the latest version by checking release, rc, and current channel version files
func GetLatestVersionForChannel(currentVersion string) (string, error) {
	result, err := GetLatestVersionForChannelDetailed(currentVersion)
	if err != nil {
		return "", err
	}
	return result.LatestVersion, nil
}

// GetLatestVersionForChannelDetailed gets the latest version with detailed information
// It always checks release, rc, and the current channel (if different)
func GetLatestVersionForChannelDetailed(currentVersion string) (*VersionCheckResult, error) {
	// Determine current channel
	currentChannel := ExtractChannel(currentVersion)
	slog.Debug("Extracting channel from version", "currentVersion", currentVersion, "channel", currentChannel)

	result := &VersionCheckResult{
		CurrentChannel:  currentChannel,
		ChannelVersions: make(map[string]string),
	}

	// Fetch versions from release, rc, and current channel
	var versions []string

	// Always check release channel
	slog.Debug("Fetching release channel version")
	if releaseVersion, err := fetchVersionFromChannel("release"); err == nil && releaseVersion != "" {
		slog.Debug("Found release version", "version", releaseVersion)
		versions = append(versions, releaseVersion)
		result.ChannelVersions["release"] = releaseVersion
	} else if err != nil {
		slog.Debug("Failed to fetch release version", "error", err)
	}

	// Always check rc channel
	slog.Debug("Fetching rc channel version")
	if rcVersion, err := fetchVersionFromChannel("rc"); err == nil && rcVersion != "" {
		slog.Debug("Found rc version", "version", rcVersion)
		versions = append(versions, rcVersion)
		result.ChannelVersions["rc"] = rcVersion
	} else if err != nil {
		slog.Debug("Failed to fetch rc version", "error", err)
	}

	// Check current channel if it's not release or rc
	if currentChannel != "release" && currentChannel != "rc" {
		slog.Debug("Fetching channel-specific version", "channel", currentChannel)
		if channelVersion, err := fetchVersionFromChannel(currentChannel); err == nil && channelVersion != "" {
			slog.Debug("Found channel version", "channel", currentChannel, "version", channelVersion)
			versions = append(versions, channelVersion)
			result.ChannelVersions[currentChannel] = channelVersion
		} else if err != nil {
			slog.Debug("Failed to fetch channel version", "channel", currentChannel, "error", err)
		}
	}

	// If no versions found, return error
	if len(versions) == 0 {
		return nil, fmt.Errorf("no versions found")
	}

	// Prefer current channel; fall back rc → release
	var chosen string
	switch currentChannel {
	case "dev":
		// Always prefer the rolling dev-latest path when on dev channel
		chosen = "dev-latest"
	case "rc":
		if v, ok := result.ChannelVersions["rc"]; ok && v != "" {
			chosen = v
		}
	default: // release
		if v, ok := result.ChannelVersions["release"]; ok && v != "" {
			chosen = v
		}
	}

	if chosen == "" {
		if v, ok := result.ChannelVersions["rc"]; ok && v != "" {
			chosen = v
		}
	}
	if chosen == "" {
		if v, ok := result.ChannelVersions["release"]; ok && v != "" {
			chosen = v
		}
	}

	if chosen == "" {
		return nil, fmt.Errorf("no valid versions found")
	}

	result.LatestVersion = chosen
	return result, nil
}

// ExtractChannel extracts the channel from a version string
func ExtractChannel(version string) string {
	// Remove 'v' prefix if present
	version = strings.TrimPrefix(version, "v")

	// Match pattern like -rc1, -dev1, etc.
	re := regexp.MustCompile(`-([a-zA-Z]+)\d*$`)
	matches := re.FindStringSubmatch(version)

	if len(matches) > 1 {
		suffix := matches[1]
		// Normalize known channel families
		if strings.HasPrefix(suffix, "dev") {
			return "dev"
		}
		if strings.HasPrefix(suffix, "rc") {
			return "rc"
		}
		return suffix
	}

	// No suffix means release channel
	return "release"
}

// fetchVersionFromChannel retrieves the version from a channel's .txt file
func fetchVersionFromChannel(channel string) (string, error) {
	url := fmt.Sprintf("https://sprites-binaries.t3.storage.dev/client/%s.txt", channel)
	slog.Debug("Fetching version from channel file", "channel", channel, "url", url)

	client := &http.Client{
		Timeout: 5 * time.Second,
	}

	resp, err := client.Get(url)
	if err != nil {
		slog.Debug("Failed to fetch channel file", "error", err)
		return "", err
	}
	defer resp.Body.Close()

	slog.Debug("Channel file response", "status", resp.StatusCode)
	if resp.StatusCode == http.StatusNotFound {
		slog.Debug("Channel file not found")
		return "", nil // Channel file doesn't exist yet
	}

	if resp.StatusCode != http.StatusOK {
		return "", fmt.Errorf("unexpected status code: %d", resp.StatusCode)
	}

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return "", err
	}

	// Trim whitespace but keep the version as-is (could have 'v' prefix)
	version := strings.TrimSpace(string(body))
	slog.Debug("Channel version retrieved", "channel", channel, "version", version)

	return version, nil
}

func listBucketVersions(bucketURL string, prefix string) (map[string]*semver.Version, error) {
	slog.Debug("Listing bucket versions", "url", bucketURL, "prefix", prefix)
	// Try to list the bucket contents
	resp, err := http.Get(bucketURL)
	if err != nil {
		return nil, fmt.Errorf("failed to fetch bucket contents: %w", err)
	}
	defer resp.Body.Close()

	slog.Debug("Bucket list response", "status", resp.StatusCode)
	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("failed to list bucket: HTTP %d", resp.StatusCode)
	}

	// Read the response body
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	// Try to parse as XML first (standard S3 response)
	var listResult S3ListResult
	if err := xml.Unmarshal(body, &listResult); err == nil {
		return parseVersionsFromObjects(listResult.Contents, prefix), nil
	}

	// If XML parsing fails, try to parse as JSON (some S3-compatible services return JSON)
	if err := json.Unmarshal(body, &listResult); err == nil {
		return parseVersionsFromObjects(listResult.Contents, prefix), nil
	}

	// If both fail, use simple string parsing as fallback
	versions := parseVersionsFromXML(string(body), prefix)
	return versions, nil
}

func parseVersionsFromObjects(objects []S3Object, prefix string) map[string]*semver.Version {
	versions := make(map[string]*semver.Version)

	for _, obj := range objects {
		// Skip entries that don't have the prefix
		if !strings.HasPrefix(obj.Key, prefix) {
			continue
		}

		// Remove prefix and extract version from key like "client/v0.0.1-rc3/sprite-darwin-arm64.tar.gz"
		keyWithoutPrefix := strings.TrimPrefix(obj.Key, prefix)
		parts := strings.Split(keyWithoutPrefix, "/")
		if len(parts) >= 2 && strings.HasPrefix(parts[0], "v") {
			versionStr := strings.TrimPrefix(parts[0], "v")
			if _, exists := versions[versionStr]; !exists {
				if v, err := semver.NewVersion(versionStr); err == nil {
					versions[versionStr] = v
				}
			}
		}
	}

	return versions
}

func parseVersionsFromXML(xmlBody string, prefix string) map[string]*semver.Version {
	versions := make(map[string]*semver.Version)

	// Simple XML parsing for S3 ListBucketResult
	// Look for <Key>client/v0.0.1-rc3/sprite-darwin-arm64.tar.gz</Key> patterns
	lines := strings.Split(xmlBody, "\n")
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if strings.HasPrefix(line, "<Key>") && strings.HasSuffix(line, "</Key>") {
			key := strings.TrimPrefix(line, "<Key>")
			key = strings.TrimSuffix(key, "</Key>")

			// Skip entries that don't have the prefix
			if !strings.HasPrefix(key, prefix) {
				continue
			}

			// Remove prefix and extract version
			keyWithoutPrefix := strings.TrimPrefix(key, prefix)
			parts := strings.Split(keyWithoutPrefix, "/")
			if len(parts) >= 2 && strings.HasPrefix(parts[0], "v") {
				versionStr := strings.TrimPrefix(parts[0], "v")
				if _, exists := versions[versionStr]; !exists {
					if v, err := semver.NewVersion(versionStr); err == nil {
						versions[versionStr] = v
					}
				}
			}
		}
	}

	return versions
}

func getPlatform() string {
	arch := runtime.GOARCH
	goos := runtime.GOOS

	// Only support amd64 and arm64
	switch arch {
	case "amd64":
		arch = "amd64"
	case "arm64":
		arch = "arm64"
	default:
		// Unsupported architecture
		fmt.Fprintf(os.Stderr, "Error: Unsupported architecture %s. Only amd64 and arm64 are supported.\n", arch)
		os.Exit(1)
	}

	return fmt.Sprintf("%s-%s", goos, arch)
}

func downloadFile(url, dest string) error {
	slog.Debug("Starting file download", "url", url, "destination", dest)
	resp, err := http.Get(url)
	if err != nil {
		slog.Debug("Download request failed", "error", err)
		return err
	}
	defer resp.Body.Close()

	slog.Debug("Download response", "status", resp.StatusCode)
	if resp.StatusCode != http.StatusOK {
		return fmt.Errorf("download failed: HTTP %d", resp.StatusCode)
	}

	out, err := os.Create(dest)
	if err != nil {
		return err
	}
	defer out.Close()

	n, err := io.Copy(out, resp.Body)
	if err != nil {
		slog.Debug("Failed to write download", "error", err)
		return err
	}
	slog.Debug("Download completed", "bytes", n)
	return nil
}

func extractTarGz(tarGzPath, destDir string) error {
	file, err := os.Open(tarGzPath)
	if err != nil {
		return err
	}
	defer file.Close()

	gzr, err := gzip.NewReader(file)
	if err != nil {
		return err
	}
	defer gzr.Close()

	tr := tar.NewReader(gzr)

	for {
		header, err := tr.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}

		// Only extract regular files named "sprite" or "sprite.exe"
		if header.Typeflag == tar.TypeReg &&
			(header.Name == "sprite" || header.Name == "sprite.exe" ||
				filepath.Base(header.Name) == "sprite" || filepath.Base(header.Name) == "sprite.exe") {

			target := filepath.Join(destDir, filepath.Base(header.Name))

			outFile, err := os.Create(target)
			if err != nil {
				return err
			}

			if _, err := io.Copy(outFile, tr); err != nil {
				outFile.Close()
				return err
			}

			outFile.Close()

			// Set file permissions
			if err := os.Chmod(target, os.FileMode(header.Mode)); err != nil {
				return err
			}
		}
	}

	return nil
}

func extractZip(zipPath, destDir string) error {
	reader, err := zip.OpenReader(zipPath)
	if err != nil {
		return err
	}
	defer reader.Close()

	for _, file := range reader.File {
		// Only extract files named "sprite" or "sprite.exe"
		if file.Name == "sprite" || file.Name == "sprite.exe" ||
			filepath.Base(file.Name) == "sprite" || filepath.Base(file.Name) == "sprite.exe" {

			target := filepath.Join(destDir, filepath.Base(file.Name))

			fileReader, err := file.Open()
			if err != nil {
				return err
			}
			defer fileReader.Close()

			outFile, err := os.Create(target)
			if err != nil {
				return err
			}
			defer outFile.Close()

			if _, err := io.Copy(outFile, fileReader); err != nil {
				return err
			}

			// Set file permissions (on non-Windows systems)
			if runtime.GOOS != "windows" {
				if err := os.Chmod(target, os.FileMode(file.Mode())); err != nil {
					return err
				}
			}
		}
	}

	return nil
}

func replaceExecutable(oldPath, newPath string) error {
	// On Windows, we need to rename the old executable first
	if runtime.GOOS == "windows" {
		backupPath := oldPath + ".old"

		// Remove any existing backup
		os.Remove(backupPath)

		// Rename current executable to backup
		if err := os.Rename(oldPath, backupPath); err != nil {
			return fmt.Errorf("failed to backup current executable: %w", err)
		}

		// Move new executable to the original path
		if err := os.Rename(newPath, oldPath); err != nil {
			// Try to restore the backup
			os.Rename(backupPath, oldPath)
			return fmt.Errorf("failed to install new executable: %w", err)
		}

		// Remove the backup
		os.Remove(backupPath)
	} else {
		// On Unix-like systems, we can directly replace
		if err := os.Rename(newPath, oldPath); err != nil {
			return fmt.Errorf("failed to replace executable: %w", err)
		}
	}

	return nil
}

// isRemoteArchiveNewer checks the remote archive's Last-Modified against the local executable's timestamp.
// Returns true if remote is newer. If Last-Modified is missing or unparsable, returns true to allow refresh.
func isRemoteArchiveNewer(url, localPath string) (bool, error) {
	client := &http.Client{Timeout: 5 * time.Second}
	req, err := http.NewRequest("HEAD", url, nil)
	if err != nil {
		return false, err
	}
	resp, err := client.Do(req)
	if err != nil {
		return false, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return false, fmt.Errorf("unexpected status code: %d", resp.StatusCode)
	}

	lm := resp.Header.Get("Last-Modified")
	if lm == "" {
		return true, nil
	}
	remoteTime, err := http.ParseTime(lm)
	if err != nil {
		return true, nil
	}

	localTime, err := getFileCreateTimeOrMTime(localPath)
	if err != nil {
		return false, err
	}

	return remoteTime.After(localTime), nil
}

// getFileCreateTimeOrMTime returns the file creation time if available; otherwise falls back to modification time.
// Note: portable fallback uses ModTime, as creation time is not universally available across platforms.
func getFileCreateTimeOrMTime(path string) (time.Time, error) {
	info, err := os.Stat(path)
	if err != nil {
		return time.Time{}, err
	}
	// Portable fallback
	return info.ModTime(), nil
}
