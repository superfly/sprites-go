//go:build releaser_manual

package main

import (
	"bytes"
	"os/exec"
	"strings"
	"testing"
)

func runCmd(t *testing.T, name string, args ...string) string {
	t.Helper()
	cmd := exec.Command(name, args...)
	var out bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &out
	if err := cmd.Run(); err != nil {
		t.Fatalf("%s failed: %v\n%s", name, err, out.String())
	}
	return out.String()
}

// Verify that running the context command succeeds under this repo checkout
func TestContextDevMode_Manual(t *testing.T) {
	t.Setenv("GITHUB_REF_TYPE", "branch")
	t.Setenv("GITHUB_REF_NAME", "dev-release")
	out := runCmd(t, "go", "run", ".", "context")
	if !strings.Contains(out, "\"Mode\": \"dev\"") && !strings.Contains(out, "\"Mode\":\"dev\"") {
		t.Fatalf("expected dev mode in output, got: %s", out)
	}
}
