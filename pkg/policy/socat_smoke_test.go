//go:build linux
// +build linux

package policy

import (
	"context"
	"os/exec"
	"strings"
	"testing"
	"time"
)

func runCmd(t *testing.T, timeout time.Duration, name string, args ...string) (string, error) {
	t.Helper()
	ctx, cancel := context.WithTimeout(context.Background(), timeout)
	defer cancel()
	cmd := exec.CommandContext(ctx, name, args...)
	out, err := cmd.CombinedOutput()
	return string(out), err
}

func TestSocatSmoke(t *testing.T) {
	t.Log("starting socat/netcat smoke test with -v output")
	// Start IPv4 responder (netcat-loop)
	if _, err := runCmd(t, 3*time.Second, "sh", "-lc",
		`(while true; do printf 'HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok' | nc -4 -l -p 18080 -q 1; done) >/tmp/s4.log 2>&1 & echo $! > /tmp/s4.pid`); err != nil {
		t.Fatalf("failed to start ipv4 listener: %v", err)
	}
	// Start IPv6 responder (netcat-loop)
	if _, err := runCmd(t, 3*time.Second, "sh", "-lc",
		`(while true; do printf 'HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok' | nc -6 -l -p 18081 -q 1; done) >/tmp/s6.log 2>&1 & echo $! > /tmp/s6.pid`); err != nil {
		t.Fatalf("failed to start ipv6 listener: %v", err)
	}
	t.Cleanup(func() {
		_, _ = runCmd(t, 2*time.Second, "sh", "-lc", "kill $(cat /tmp/s4.pid 2>/dev/null) 2>/dev/null || true")
		_, _ = runCmd(t, 2*time.Second, "sh", "-lc", "kill $(cat /tmp/s6.pid 2>/dev/null) 2>/dev/null || true")
	})

	// Give listeners a moment to bind
	time.Sleep(200 * time.Millisecond)

	// Verify IPv4 listener appears
	if out, _ := runCmd(t, 2*time.Second, "sh", "-lc", `ss -4 -ltn | awk '{print $4}' | grep -E ':18080$' || true`); !strings.Contains(out, ":18080") {
		log4, _ := runCmd(t, 1*time.Second, "sh", "-lc", "[ -f /tmp/s4.log ] && cat /tmp/s4.log || true")
		t.Fatalf("ipv4 listener not ready; ss: %q\nlog:\n%s", out, log4)
	}

	// Verify IPv6 listener appears
	if out, _ := runCmd(t, 2*time.Second, "sh", "-lc", `ss -6 -ltn | awk '{print $4}' | grep -E '(:|\])18081$' || true`); !strings.Contains(out, ":18081") {
		log6, _ := runCmd(t, 1*time.Second, "sh", "-lc", "[ -f /tmp/s6.log ] && cat /tmp/s6.log || true")
		t.Fatalf("ipv6 listener not ready; ss: %q\nlog:\n%s", out, log6)
	}

	// Connect to IPv4 server
	if out, err := runCmd(t, 3*time.Second, "sh", "-lc", `curl -sS --max-time 2 http://127.0.0.1:18080`); err != nil || strings.TrimSpace(out) != "ok" {
		t.Fatalf("curl ipv4 failed: err=%v out=%q", err, out)
	}

	// Connect to IPv6 server
	if out, err := runCmd(t, 3*time.Second, "sh", "-lc", `curl -g -6 -sS --max-time 2 http://[::1]:18081`); err != nil || strings.TrimSpace(out) != "ok" {
		t.Fatalf("curl ipv6 failed: err=%v out=%q", err, out)
	}
}
