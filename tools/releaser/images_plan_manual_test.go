//go:build releaser_manual

package main

import (
	"bytes"
	"encoding/json"
	"os"
	"os/exec"
	"strings"
	"testing"
)

type planOut struct {
	Base struct {
		Action string `json:"action"`
		Source string `json:"sourceTag"`
		Target string `json:"targetTag"`
	} `json:"base"`
	Languages struct {
		Action string `json:"action"`
		Source string `json:"sourceTag"`
		Target string `json:"targetTag"`
	} `json:"languages"`
	ServerTag string `json:"serverTag"`
}

func runJSON(t *testing.T, name string, args ...string) planOut {
	t.Helper()
	cmd := exec.Command(name, args...)
	var out bytes.Buffer
	cmd.Stdout = &out
	cmd.Stderr = &out
	if err := cmd.Run(); err != nil {
		t.Fatalf("%s failed: %v\n%s", name, err, out.String())
	}
	var p planOut
	if err := json.Unmarshal(out.Bytes(), &p); err != nil {
		t.Fatalf("json decode: %v\n%s", err, out.String())
	}
	return p
}

func TestImagesPlan_Manual(t *testing.T) {
	// Allow overriding the diff window to a narrow range for quick checks
	os.Setenv("RELEASER_DIFF_SINCE", "HEAD^")
	os.Setenv("RELEASER_DIFF_UNTIL", "HEAD")
	p := runJSON(t, "go", "run", ".", "images", "plan", "--registry", "ghcr.io", "--ubuntu-image", "superfly/sprite-ubuntu", "--distro", "25.04")
	if p.ServerTag == "" || !strings.Contains(p.Languages.Target, "25.04-") {
		t.Fatalf("unexpected plan: %+v", p)
	}
}
