//go:build releaser_manual

package main

import (
	"bytes"
	"encoding/json"
	"os/exec"
	"testing"

	"github.com/google/go-containerregistry/pkg/authn"
	"github.com/google/go-containerregistry/pkg/name"
	"github.com/google/go-containerregistry/pkg/v1/remote"
)

type ctxOut struct {
	Previous string `json:"previous_tag"`
}

type planOut2 struct {
	Base struct {
		Action string `json:"action"`
		Source string `json:"sourceTag"`
		Target string `json:"targetTag"`
	} `json:"base"`
}

func ghcrTagExists(t *testing.T, repo, tag string) bool {
	t.Helper()
	ref, err := name.ParseReference("ghcr.io/" + repo + ":" + tag)
	if err != nil {
		return false
	}
	if _, err := remote.Index(ref, remote.WithAuthFromKeychain(authn.DefaultKeychain)); err == nil {
		return true
	}
	if _, err := remote.Image(ref, remote.WithAuthFromKeychain(authn.DefaultKeychain)); err == nil {
		return true
	}
	return false
}

func runJSONOut(t *testing.T, args ...string) []byte {
	t.Helper()
	cmd := exec.Command("go", append([]string{"run", "."}, args...)...)
	var out bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &out
	if err := cmd.Run(); err != nil {
		t.Fatalf("go run . %v failed: %v\n%s", args, err, out.String())
	}
	return out.Bytes()
}

// If no changes (forced via diff window) and the previous source image exists, we should retag from previous.
func TestShouldRetagFromPrevious_NoChanges_Prod(t *testing.T) {
	t.Setenv("GITHUB_REF_TYPE", "tag")
	t.Setenv("GITHUB_REF_NAME", "v0.0.0") // synthetic target; unlikely to exist
	t.Setenv("RELEASER_DIFF_SINCE", "HEAD")
	t.Setenv("RELEASER_DIFF_UNTIL", "HEAD")

	// Get previous tag from context
	ctxBytes := runJSONOut(t, "context")
	var c ctxOut
	if err := json.Unmarshal(ctxBytes, &c); err != nil {
		t.Fatalf("decode context: %v\n%s", err, string(ctxBytes))
	}
	if c.Previous == "" {
		t.Skip("no previous semver tag reachable; skipping")
	}
	prevBase := "25.04-" + c.Previous
	if !ghcrTagExists(t, "superfly/sprite-ubuntu", prevBase) {
		t.Skip("previous base image not found in registry; skipping")
	}

	pBytes := runJSONOut(t, "images", "plan", "--registry", "ghcr.io", "--ubuntu-image", "superfly/sprite-ubuntu", "--distro", "25.04")
	var p planOut2
	if err := json.Unmarshal(pBytes, &p); err != nil {
		t.Fatalf("decode plan: %v\n%s", err, string(pBytes))
	}
	if p.Base.Action != "retag" || p.Base.Source != prevBase {
		t.Fatalf("expected retag from %s, got action=%s source=%s plan=%s", prevBase, p.Base.Action, p.Base.Source, string(pBytes))
	}
}

// If there are changes (diff across a wider window) and the target tag does not already exist, we should build.
func TestShouldBuild_WhenChanges_Prod(t *testing.T) {
	t.Setenv("GITHUB_REF_TYPE", "tag")
	t.Setenv("GITHUB_REF_NAME", "v0.0.0") // synthetic target; unlikely to exist
	// Widen diff window to increase likelihood of change detection
	t.Setenv("RELEASER_DIFF_SINCE", "HEAD~50")
	t.Setenv("RELEASER_DIFF_UNTIL", "HEAD")

	// Ensure target does not already exist; if it does, this environment is unexpected for this test.
	// Derive target from plan output itself for comparison.
	pBytes := runJSONOut(t, "images", "plan", "--registry", "ghcr.io", "--ubuntu-image", "superfly/sprite-ubuntu", "--distro", "25.04")
	var p planOut2
	if err := json.Unmarshal(pBytes, &p); err != nil {
		t.Fatalf("decode plan: %v\n%s", err, string(pBytes))
	}
	if ghcrTagExists(t, "superfly/sprite-ubuntu", p.Base.Target) {
		t.Skip("target tag unexpectedly exists in registry; skipping to avoid nondeterminism")
	}
	if p.Base.Action != "build" {
		t.Fatalf("expected build due to detected changes, got action=%s plan=%s", p.Base.Action, string(pBytes))
	}
}

// For dev, with no changes, if previous exists we should retag-from-previous.
func TestShouldRetagFromPrevious_NoChanges_Dev(t *testing.T) {
	t.Setenv("GITHUB_REF_TYPE", "branch")
	t.Setenv("GITHUB_REF_NAME", "dev-release")
	t.Setenv("RELEASER_DIFF_SINCE", "HEAD")
	t.Setenv("RELEASER_DIFF_UNTIL", "HEAD")

	// Determine previous from context
	ctxBytes := runJSONOut(t, "context")
	var c ctxOut
	if err := json.Unmarshal(ctxBytes, &c); err != nil {
		t.Fatalf("decode context: %v", err)
	}
	if c.Previous == "" {
		t.Skip("no previous semver tag; skipping")
	}
	prevBase := "25.04-" + c.Previous
	if !ghcrTagExists(t, "superfly/sprite-ubuntu", prevBase) {
		t.Skip("previous base image missing; skipping")
	}

	pBytes := runJSONOut(t, "images", "plan", "--registry", "ghcr.io", "--ubuntu-image", "superfly/sprite-ubuntu", "--distro", "25.04")
	var p planOut2
	if err := json.Unmarshal(pBytes, &p); err != nil {
		t.Fatalf("decode plan: %v", err)
	}
	if p.Base.Action != "retag" || p.Base.Source != prevBase {
		t.Fatalf("expected retag from %s for dev no-changes, got %q", prevBase, pBytes)
	}
}

// For dev, with changes and non-existent target, we should build (retag-from-target allowed if it already exists).
func TestShouldBuild_WhenChanges_Dev(t *testing.T) {
	t.Setenv("GITHUB_REF_TYPE", "branch")
	t.Setenv("GITHUB_REF_NAME", "dev-release")
	t.Setenv("RELEASER_DIFF_SINCE", "HEAD~50")
	t.Setenv("RELEASER_DIFF_UNTIL", "HEAD")

	pBytes := runJSONOut(t, "images", "plan", "--registry", "ghcr.io", "--ubuntu-image", "superfly/sprite-ubuntu", "--distro", "25.04")
	var p planOut2
	if err := json.Unmarshal(pBytes, &p); err != nil {
		t.Fatalf("decode plan: %v", err)
	}
	if ghcrTagExists(t, "superfly/sprite-ubuntu", p.Base.Target) {
		t.Skip("target exists; retag-from-target is acceptable; skipping")
	}
	if p.Base.Action != "build" {
		t.Fatalf("expected build for dev with changes and missing target; got %q", pBytes)
	}
}
