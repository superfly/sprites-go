package policy

import (
	"context"
	"fmt"
	"math/rand"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// Test that the policy manager creates the container netns and the /run/netns/<name> entry
func TestManagerCreatesNetnsSymlink(t *testing.T) {
	if os.Geteuid() != 0 {
		t.Skip("root required")
	}
	if _, err := exec.LookPath("ip"); err != nil {
		t.Skip("ip command not available")
	}

	ns := "sprite"
	// Cleanup any pre-existing namespace/symlink
	_ = os.Remove(filepath.Join("/run/netns", ns))
	_ = exec.Command("sh", "-lc", fmt.Sprintf("ip netns delete %s 2>/dev/null || true", ns)).Run()

	// Unique interface names to avoid collisions
	rand.Seed(time.Now().UnixNano())
	ifHost := fmt.Sprintf("sprtest%d", rand.Intn(1_000_000))
	ifPeer := fmt.Sprintf("sprpeer%d", rand.Intn(1_000_000))

	cfg := BootConfig{
		ContainerNS:    ns,
		IfName:         ifHost,
		PeerIfName:     ifPeer,
		IfIPv4:         net.ParseIP("10.222.0.1"),
		PeerIPv4:       net.ParseIP("10.222.0.2"),
		IPv4MaskLen:    24,
		IfIPv6:         net.ParseIP("fd00:222::1"),
		PeerIPv6:       net.ParseIP("fd00:222::2"),
		IPv6MaskLen:    64,
		DnsPort:        53,
		HostResolvPath: filepath.Join(os.TempDir(), "resolv.test"),
		Mode:           Unrestricted,
		EnableIPv6:     true,
		TableName:      "sprite_egress_test",
		SetV4:          "allowed_v4_test",
		SetV6:          "allowed_v6_test",
	}

	m := NewManager(cfg)
	ctx, cancel := context.WithTimeout(context.Background(), 15*time.Second)
	defer cancel()

	if err := m.Start(ctx); err != nil {
		t.Fatalf("manager start failed: %v", err)
	}
	defer m.Stop(context.Background())

	// Assert /run/netns/sprite exists
	p := filepath.Join("/run/netns", ns)
	if _, err := os.Stat(p); err != nil {
		t.Fatalf("expected %s to exist, got error: %v", p, err)
	}
	// Assert ip netns list contains the namespace
	out, err := exec.Command("sh", "-lc", "ip netns list | awk '{print $1}'").Output()
	if err != nil {
		t.Fatalf("ip netns list failed: %v", err)
	}
	if !containsWord(string(out), ns) {
		t.Fatalf("expected netns %s in 'ip netns list', got: %s", ns, string(out))
	}
}

func containsWord(s, w string) bool {
	return strings.Contains(s, w)
}
