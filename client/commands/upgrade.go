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
	"net/http"
	"os"
	"path/filepath"
	"regexp"
	"runtime"
	"strings"
	"time"

	"github.com/superfly/sprite-env/client/config"

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

	// Check if we should do a version check
	if !force && !shouldCheckVersion(cfg) && !checkOnly {
		fmt.Println("Version check performed recently. Use --force to check again.")
		return nil
	}

	fmt.Println("Checking for updates...")

	// Find the latest version or the target version
	var selectedVersion *semver.Version
	var selectedVersionStr string
	if targetVersion != "" {
		// Find specific version - need to list all versions
		versions, err := listBucketVersions(bucketURL, clientPrefix)
		if err != nil {
			return fmt.Errorf("failed to list versions: %w", err)
		}

		if len(versions) == 0 {
			return fmt.Errorf("no versions found in the bucket")
		}

		for vStr, v := range versions {
			if vStr == targetVersion {
				selectedVersion = v
				selectedVersionStr = vStr
				break
			}
		}
		if selectedVersion == nil {
			return fmt.Errorf("version %s not found", targetVersion)
		}
	} else {
		// Get the latest version using channel-based check
		currentVersion := cfg.GetCurrentVersion()
		if currentVersion == "" {
			currentVersion = globalCtx.Version
		}

		latestVersionStr, err := GetLatestVersionForChannel(currentVersion)
		if err != nil {
			return fmt.Errorf("failed to get latest version: %w", err)
		}

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

	// Get current version - use embedded version as fallback
	currentVersion := cfg.GetCurrentVersion()
	if currentVersion == "" && globalCtx.Version != "" {
		currentVersion = globalCtx.Version
	}
	if currentVersion != "" {
		fmt.Printf("Current version: %s\n", currentVersion)
	}

	// Check if current version is a dev version
	isDevVersion := strings.HasSuffix(currentVersion, "-dev")

	if checkOnly {
		if currentVersion != "" {
			if isDevVersion {
				fmt.Printf("You are running a development version (%s).\n", currentVersion)
				fmt.Printf("Latest release version: %s\n", selectedVersionStr)
			} else if currentVersion == selectedVersionStr {
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
			baseVersion := strings.TrimSuffix(currentVersion, "-dev")
			if strings.HasPrefix(selectedVersionStr, baseVersion) {
				fmt.Printf("You are running a development version (%s) which is newer than the latest release (%s).\n", currentVersion, selectedVersionStr)
				fmt.Println("Use --force to downgrade to the release version.")
				return nil
			}
		} else if currentVersion == selectedVersionStr {
			fmt.Println("Already running the latest version.")
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
	downloadURL := fmt.Sprintf("%s%sv%s/%s", bucketURL, clientPrefix, selectedVersionStr, binaryName)

	fmt.Printf("Downloading %s...\n", binaryName)

	// Create temporary directory
	tempDir, err := os.MkdirTemp("", "sprite-upgrade-*")
	if err != nil {
		return fmt.Errorf("failed to create temp directory: %w", err)
	}
	defer os.RemoveAll(tempDir)

	// Download the binary
	tempFile := filepath.Join(tempDir, binaryName)
	if err := downloadFile(downloadURL, tempFile); err != nil {
		return fmt.Errorf("failed to download: %w", err)
	}

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
	if err := replaceExecutable(currentExe, extractedBinary); err != nil {
		return fmt.Errorf("failed to replace executable: %w", err)
	}

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

// GetLatestVersionForChannel gets the latest version by checking channel version files
func GetLatestVersionForChannel(currentVersion string) (string, error) {
	result, err := GetLatestVersionForChannelDetailed(currentVersion)
	if err != nil {
		return "", err
	}
	return result.LatestVersion, nil
}

// GetLatestVersionForChannelDetailed gets the latest version with detailed information
func GetLatestVersionForChannelDetailed(currentVersion string) (*VersionCheckResult, error) {
	// Determine current channel
	currentChannel := ExtractChannel(currentVersion)

	result := &VersionCheckResult{
		CurrentChannel:  currentChannel,
		ChannelVersions: make(map[string]string),
	}

	// Fetch versions from both current channel and release channel
	var versions []string

	// Always check release channel
	if releaseVersion, err := fetchVersionFromChannel("release"); err == nil && releaseVersion != "" {
		versions = append(versions, releaseVersion)
		result.ChannelVersions["release"] = releaseVersion
	}

	// Check current channel if it's not release
	if currentChannel != "release" {
		if channelVersion, err := fetchVersionFromChannel(currentChannel); err == nil && channelVersion != "" {
			versions = append(versions, channelVersion)
			result.ChannelVersions[currentChannel] = channelVersion
		}
	}

	// If no versions found, return error
	if len(versions) == 0 {
		return nil, fmt.Errorf("no versions found")
	}

	// Find the highest version
	var highestVersion *semver.Version
	var highestVersionStr string

	for _, versionStr := range versions {
		// Remove v prefix for semver parsing
		cleanVersion := strings.TrimPrefix(versionStr, "v")
		v, err := semver.NewVersion(cleanVersion)
		if err != nil {
			continue
		}

		if highestVersion == nil || v.GreaterThan(highestVersion) {
			highestVersion = v
			highestVersionStr = versionStr // Keep original format (with v if present)
		}
	}

	if highestVersionStr == "" {
		return nil, fmt.Errorf("no valid versions found")
	}

	result.LatestVersion = highestVersionStr
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
		return matches[1]
	}

	// No suffix means release channel
	return "release"
}

// fetchVersionFromChannel retrieves the version from a channel's .txt file
func fetchVersionFromChannel(channel string) (string, error) {
	url := fmt.Sprintf("https://sprites-binaries.t3.storage.dev/client/%s.txt", channel)

	client := &http.Client{
		Timeout: 5 * time.Second,
	}

	resp, err := client.Get(url)
	if err != nil {
		return "", err
	}
	defer resp.Body.Close()

	if resp.StatusCode == http.StatusNotFound {
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

	return version, nil
}

func listBucketVersions(bucketURL string, prefix string) (map[string]*semver.Version, error) {
	// Try to list the bucket contents
	resp, err := http.Get(bucketURL)
	if err != nil {
		return nil, fmt.Errorf("failed to fetch bucket contents: %w", err)
	}
	defer resp.Body.Close()

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
	resp, err := http.Get(url)
	if err != nil {
		return err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return fmt.Errorf("download failed: HTTP %d", resp.StatusCode)
	}

	out, err := os.Create(dest)
	if err != nil {
		return err
	}
	defer out.Close()

	_, err = io.Copy(out, resp.Body)
	return err
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
