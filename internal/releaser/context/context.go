package context

import (
	"bytes"
	"context"
	"fmt"
	"os"
	"os/exec"
	"regexp"
	"strings"

	semver "github.com/Masterminds/semver/v3"
)

type Context struct {
	RefType  string
	RefName  string
	SHA      string
	ShortSHA string
}

// Output is the computed, workflow-friendly context
type Output struct {
	Mode               string // "prod" for tag releases, "dev" for main
	Version            string // X.Y.Z (without 'v') for tag releases
	DevVersion         string // X.Y.Z-dev-<shortsha> for dev
	UbuntuTag          string // e.g., 25.04-X.Y.Z or 25.04-X.Y.Z-dev-<sha>
	UbuntuLanguagesTag string // UbuntuTag + "-languages"
	ServerTag          string // X.Y.Z or dev string
	IsVersionTag       bool
	PreviousTagNoV     string // previous semver tag without 'v'
	TagLatestBase      bool
	TagLatestLang      bool
	TagLatestServer    bool
	ShortSHA           string

	// For bash S3 steps in workflows
	ClientUploadPrefix string // e.g., client/vX.Y.Z/ or client/dev-latest/
	ClientChannelFile  string // e.g., release.txt, rc.txt, dev.txt
	ClientChannelValue string // value to write into the channel file
}

func getenv(k, d string) string {
	v := os.Getenv(k)
	if v == "" {
		return d
	}
	return v
}

func runGit(args ...string) (string, error) {
	cmd := exec.Command("git", args...)
	var out bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &out
	if err := cmd.Run(); err != nil {
		return "", fmt.Errorf("git %v: %w: %s", strings.Join(args, " "), err, out.String())
	}
	return strings.TrimSpace(out.String()), nil
}

func headSHA() (string, error) {
	return runGit("rev-parse", "HEAD")
}

func currentRef() (string, error) {
	// Prefer branch name; fallback to tag description
	if ref, err := runGit("rev-parse", "--abbrev-ref", "HEAD"); err == nil && ref != "HEAD" {
		return ref, nil
	}
	// Last tag name
	if tag, err := runGit("describe", "--tags", "--abbrev=0"); err == nil {
		return tag, nil
	}
	return "", nil
}

func latestSemverTag() (string, error) {
	// Use git describe to find the latest vX.Y.Z tag reachable from HEAD
	tag, err := runGit("describe", "--tags", "--abbrev=0", "--match", "v[0-9]*.[0-9]*.[0-9]*")
	if err != nil {
		return "", nil // treat as not found
	}
	return tag, nil
}

func previousSemverTagFromHeadParent() (string, error) {
	tag, err := runGit("describe", "--tags", "--abbrev=0", "HEAD^")
	if err != nil {
		return "", nil
	}
	return tag, nil
}

// Derive reads env and git to build a raw Context
func Derive(ctx context.Context) (*Context, error) {
	refType := getenv("GITHUB_REF_TYPE", "")
	refName := getenv("GITHUB_REF_NAME", "")
	sha := getenv("GITHUB_SHA", "")
	if sha == "" {
		var err error
		sha, err = headSHA()
		if err != nil {
			return nil, err
		}
	}
	if refName == "" {
		rn, _ := currentRef()
		refName = rn
	}
	short := sha
	if len(short) > 7 {
		short = short[:7]
	}
	return &Context{RefType: refType, RefName: refName, SHA: sha, ShortSHA: short}, nil
}

// RenderContext converts the raw GitHub/git context into release-oriented outputs
func RenderContext(c Context, distro string) Output {
	out := Output{ShortSHA: c.ShortSHA}
	// Determine mode
	if c.RefType == "tag" && strings.HasPrefix(c.RefName, "v") {
		out.Mode = "prod"
		out.IsVersionTag = true
		version := strings.TrimPrefix(c.RefName, "v")
		out.Version = version
		out.ServerTag = version
		out.UbuntuTag = fmt.Sprintf("%s-%s", distro, version)
		out.UbuntuLanguagesTag = out.UbuntuTag + "-languages"
		// previous tag
		if t, _ := previousSemverTagFromHeadParent(); t != "" {
			out.PreviousTagNoV = strings.TrimPrefix(t, "v")
		}
		// latest flags (only if no prerelease suffix)
		prere := regexp.MustCompile(`-`)
		if !prere.MatchString(c.RefName) {
			out.TagLatestBase = true
			out.TagLatestLang = true
			out.TagLatestServer = true
		}
		// client channel & upload prefix
		// Determine channel name (default release). If prerelease, use letters in suffix (rc, beta, etc.).
		channel := "release"
		if i := strings.Index(version, "-"); i != -1 {
			suf := version[i+1:]
			letters := regexp.MustCompile(`[A-Za-z]+`).FindString(suf)
			if letters != "" {
				channel = strings.ToLower(letters)
			}
		}
		out.ClientUploadPrefix = fmt.Sprintf("client/v%s/", version)
		out.ClientChannelFile = channel + ".txt"
		out.ClientChannelValue = "v" + version
		return out
	}

	// Default to dev (main or other branches)
	out.Mode = "dev"
	// Find latest semver tag and compute next patch
	latest, _ := latestSemverTag()
	baseVersion := "0.0.0"
	if latest != "" {
		v, err := semver.NewVersion(strings.TrimPrefix(latest, "v"))
		if err == nil {
			nv := v.IncPatch()
			baseVersion = nv.String()
		}
		out.PreviousTagNoV = strings.TrimPrefix(latest, "v")
	} else {
		baseVersion = "0.0.1"
	}
	out.DevVersion = fmt.Sprintf("%s-dev-%s", baseVersion, c.ShortSHA)
	out.ServerTag = out.DevVersion
	out.UbuntuTag = fmt.Sprintf("%s-%s", distro, out.DevVersion)
	out.UbuntuLanguagesTag = out.UbuntuTag + "-languages"
	// latest flags all false for dev
	out.ClientUploadPrefix = "client/dev-latest/"
	out.ClientChannelFile = "dev.txt"
	out.ClientChannelValue = out.DevVersion
	return out
}

// DiffPathsSince returns true if there are any changes in the given paths between sinceRef and untilRef (default "HEAD").
func DiffPathsSince(sinceRef, untilRef string, paths []string) (bool, error) {
	if strings.TrimSpace(sinceRef) == "" {
		return true, nil
	}
	if strings.TrimSpace(untilRef) == "" {
		untilRef = "HEAD"
	}
	args := []string{"diff", "--name-only", sinceRef, untilRef, "--"}
	args = append(args, paths...)
	out, err := runGit(args...)
	if err != nil {
		// If diff fails (e.g., ref not found), assume changes to be safe
		return true, nil
	}
	return strings.TrimSpace(out) != "", nil
}
