package policy

import (
	"context"
	"fmt"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"strings"

	"github.com/fsnotify/fsnotify"
	"github.com/superfly/sprite-env/pkg/tap"
)

// PolicyMode controls whether egress is enforced.
type PolicyMode string

const (
	// Unrestricted disables nft-based egress enforcement.
	Unrestricted PolicyMode = "unrestricted"
	// DefaultRestricted applies default allowlist plus any ExtraAllow domains.
	DefaultRestricted PolicyMode = "default"
)

// BootConfig describes early networking and policy setup for a single container.
type BootConfig struct {
	// ContainerNS is the name of the container's network namespace (e.g., "sprite").
	ContainerNS string

	// OpsNetns is the namespace to host control-plane (dnsmasq/nftables). Leave empty to use root host ns.
	OpsNetns string

	// IfName is the host-side interface name (veth/tap) to which policy applies.
	IfName string
	// PeerIfName is the interface name inside the container namespace (e.g., "eth0").
	PeerIfName string

	// Host IPv4/IPv6 addresses for IfName (without CIDR). Container peer addresses as well.
	IfIPv4      net.IP
	IfIPv6      net.IP
	PeerIPv4    net.IP
	PeerIPv6    net.IP
	IPv4MaskLen int // e.g., 24
	IPv6MaskLen int // e.g., 64

	// DNS listen port (usually 53). Used when restricted mode runs dnsmasq.
	DnsPort int

	// HostResolvPath, if set, also writes resolv.conf to a host path that may be bind-mounted
	// into the container (e.g., $SPRITE_WRITE_DIR/container/resolv.conf).
	HostResolvPath string

	// ConfigDir holds the directory containing network.json. If empty, manager uses Mode/ExtraAllow.
	ConfigDir string

	// Policy specification
	Mode       PolicyMode
	ExtraAllow []string
	EnableIPv6 bool

	// Unique names for nftables artifacts (when restricted)
	TableName string
	SetV4     string
	SetV6     string
}

// Manager performs early network setup and attaches egress policy.
type Manager struct {
	cfg     BootConfig
	egress  EgressPolicyManager
	watcher *fsnotify.Watcher
}

// NewManager creates a new boot manager.
func NewManager(cfg BootConfig) *Manager {
	if cfg.DnsPort == 0 {
		cfg.DnsPort = 53
	}
	return &Manager{cfg: cfg}
}

// Start performs idempotent network setup and, if restricted, starts dnsmasq and nft policy.
func (m *Manager) Start(ctx context.Context) error {
	_ = tap.Logger(ctx).With("component", "policy", "manager", "boot")

	// Ensure container namespace exists
	if err := m.ensureNetns(ctx, m.cfg.ContainerNS); err != nil {
		return err
	}

	// Create veth pair and assign addresses/routes
	if err := m.ensureVeth(ctx); err != nil {
		return err
	}

	// Do not manage resolv.conf from policy manager; container bind-mount provides it.

	// Apply initial policy from JSON (if present) or BootConfig
	if err := m.applyPolicyFromConfig(ctx); err != nil {
		return err
	}

	// Write example configs for convenience
	if strings.TrimSpace(m.cfg.ConfigDir) != "" {
		_ = m.writeExampleConfigs()
	}

	// Start fsnotify watcher if ConfigDir set
	if strings.TrimSpace(m.cfg.ConfigDir) != "" {
		w, err := WatchNetworkConfig(ctx, m.cfg.ConfigDir, func() {
			_ = m.applyPolicyFromConfig(ctx)
		})
		if err != nil {
			return fmt.Errorf("watch config: %w", err)
		}
		m.watcher = w
	}
	return nil
}

// Stop tears down policy (network devices/namespace remain to be torn down by caller lifecycle).
func (m *Manager) Stop(ctx context.Context) {
	if m.egress != nil {
		_ = m.egress.Stop(ctx)
	}
	if m.watcher != nil {
		_ = m.watcher.Close()
	}
}

// ensureNetns creates netns if missing.
func (m *Manager) ensureNetns(ctx context.Context, ns string) error {
	if ns == "" {
		return fmt.Errorf("container netns name required")
	}

	// Create namespace in default location (/var/run/netns)
	cmd := exec.Command("sh", "-lc", fmt.Sprintf("ip netns list | awk '{print $1}' | grep -w %s >/dev/null 2>&1 || ip netns add %s", ns, ns))
	if err := cmd.Run(); err != nil {
		return fmt.Errorf("ensure netns %s: %w", ns, err)
	}

	// Create symlink for crun compatibility
	cmd = exec.Command("sh", "-lc", fmt.Sprintf("mkdir -p /run/netns && [ ! -e /run/netns/%s ] && ln -sf /var/run/netns/%s /run/netns/%s", ns, ns, ns))
	_ = cmd.Run() // Don't fail if symlink already exists

	return nil
}

// ensureVeth creates veth pair and assigns IPs/routes idempotently.
func (m *Manager) ensureVeth(ctx context.Context) error {
	if m.cfg.IfName == "" || m.cfg.PeerIfName == "" {
		return fmt.Errorf("IfName and PeerIfName required")
	}
	host := m.cfg.IfName
	peer := "peer-" + m.cfg.IfName
	// Create veth if missing
	_ = exec.Command("sh", "-lc", fmt.Sprintf("ip link show %s >/dev/null 2>&1 || ip link add %s type veth peer name %s", host, host, peer)).Run()
	// Move peer into container ns and rename
	if err := exec.Command("sh", "-lc", fmt.Sprintf("ip link set %s netns %s 2>/dev/null || true", peer, m.cfg.ContainerNS)).Run(); err != nil {
		return fmt.Errorf("move peer: %w", err)
	}
	if err := exec.Command("sh", "-lc", fmt.Sprintf("ip netns exec %s ip link set %s name %s 2>/dev/null || true", m.cfg.ContainerNS, peer, m.cfg.PeerIfName)).Run(); err != nil {
		return fmt.Errorf("rename peer: %w", err)
	}
	// Host addresses
	if m.cfg.IfIPv4 != nil && m.cfg.IPv4MaskLen > 0 {
		_ = exec.Command("sh", "-lc", fmt.Sprintf("ip addr show dev %s | grep -q %s/%d || ip addr add %s/%d dev %s", host, m.cfg.IfIPv4.String(), m.cfg.IPv4MaskLen, m.cfg.IfIPv4.String(), m.cfg.IPv4MaskLen, host)).Run()
	}
	if m.cfg.IfIPv6 != nil && m.cfg.IPv6MaskLen > 0 {
		_ = exec.Command("sh", "-lc", fmt.Sprintf("ip -6 addr show dev %s | grep -q %s/%d || ip -6 addr add %s/%d dev %s", host, m.cfg.IfIPv6.String(), m.cfg.IPv6MaskLen, m.cfg.IfIPv6.String(), m.cfg.IPv6MaskLen, host)).Run()
	}
	_ = exec.Command("ip", "link", "set", host, "up").Run()
	_ = exec.Command("ip", "-6", "link", "set", host, "up").Run()
	// Container addresses
	if m.cfg.PeerIPv4 != nil && m.cfg.IPv4MaskLen > 0 {
		_ = exec.Command("sh", "-lc", fmt.Sprintf("ip netns exec %s ip addr show dev %s | grep -q %s/%d || ip netns exec %s ip addr add %s/%d dev %s", m.cfg.ContainerNS, m.cfg.PeerIfName, m.cfg.PeerIPv4.String(), m.cfg.IPv4MaskLen, m.cfg.ContainerNS, m.cfg.PeerIPv4.String(), m.cfg.IPv4MaskLen, m.cfg.PeerIfName)).Run()
	}
	if m.cfg.PeerIPv6 != nil && m.cfg.IPv6MaskLen > 0 {
		_ = exec.Command("sh", "-lc", fmt.Sprintf("ip netns exec %s ip -6 addr show dev %s | grep -q %s/%d || ip netns exec %s ip -6 addr add %s/%d dev %s", m.cfg.ContainerNS, m.cfg.PeerIfName, m.cfg.PeerIPv6.String(), m.cfg.IPv6MaskLen, m.cfg.ContainerNS, m.cfg.PeerIPv6.String(), m.cfg.IPv6MaskLen, m.cfg.PeerIfName)).Run()
	}
	_ = exec.Command("ip", "netns", "exec", m.cfg.ContainerNS, "ip", "link", "set", m.cfg.PeerIfName, "up").Run()
	_ = exec.Command("ip", "netns", "exec", m.cfg.ContainerNS, "ip", "-6", "link", "set", m.cfg.PeerIfName, "up").Run()

	// Default routes inside container
	if m.cfg.IfIPv4 != nil {
		_ = exec.Command("sh", "-lc", fmt.Sprintf("ip netns exec %s ip route show | grep -q 'default via %s' || ip netns exec %s ip route add default via %s", m.cfg.ContainerNS, m.cfg.IfIPv4.String(), m.cfg.ContainerNS, m.cfg.IfIPv4.String())).Run()
	}
	if m.cfg.EnableIPv6 && m.cfg.IfIPv6 != nil {
		_ = exec.Command("sh", "-lc", fmt.Sprintf("ip netns exec %s ip -6 route show | grep -q 'default via %s' || ip netns exec %s ip -6 route add default via %s", m.cfg.ContainerNS, m.cfg.IfIPv6.String(), m.cfg.ContainerNS, m.cfg.IfIPv6.String())).Run()
	}
	return nil
}

// resolv.conf management is intentionally out of scope for this package.

func (m *Manager) writeExampleConfigs() error {
	dir := filepath.Join(m.cfg.ConfigDir, "examples")
	if err := os.MkdirAll(dir, 0755); err != nil {
		return err
	}
	writeIfMissing := func(name, content string) {
		path := filepath.Join(dir, name)
		if _, err := os.Stat(path); err == nil {
			return
		}
		_ = os.WriteFile(path, []byte(content+"\n"), 0644)
	}
	// 1) unrestricted
	writeIfMissing("network.unrestricted.json", `{
  "mode": "unrestricted",
  "domains": []
}`)
	// 2) defaults
	writeIfMissing("network.defaults.json", `{
  "mode": "defaults",
  "domains": []
}`)
	// 3) custom: sprites.dev and api.sprites.dev
	writeIfMissing("network.custom.json", `{
  "mode": "custom",
  "domains": [
    { "domain": "sprites.dev", "action": "allow" },
    { "domain": "api.sprites.dev", "action": "allow" }
  ]
}`)
	// 4) custom + defaults
	writeIfMissing("network.custom_plus_defaults.json", `{
  "mode": "custom_plus_defaults",
  "domains": [
    { "domain": "sprites.dev", "action": "allow" },
    { "domain": "api.sprites.dev", "action": "allow" }
  ]
}`)
	return nil
}

func (m *Manager) effectivePolicyFromBoot() (PolicyMode, []string) {
	pm := m.cfg.Mode
	var allow []string
	switch pm {
	case Unrestricted:
	case DefaultRestricted:
		allow = append(allow, DefaultAllowedDomains()...)
		if len(m.cfg.ExtraAllow) > 0 {
			allow = append(allow, m.cfg.ExtraAllow...)
		}
	default:
		// treat unknown as unrestricted
		pm = Unrestricted
	}
	return pm, allow
}

func (m *Manager) applyPolicyFromConfig(ctx context.Context) error {
	// Determine mode/allowlist
	var pm PolicyMode
	var allow []string
	if m.cfg.ConfigDir != "" {
		if _, err := os.Stat(filepath.Join(m.cfg.ConfigDir, "network.json")); err == nil {
			mode, list, err := LoadNetworkConfig(m.cfg.ConfigDir)
			if err == nil {
				pm, allow = mode, list
			} else {
				// fall back to boot
				pm, allow = m.effectivePolicyFromBoot()
			}
		} else {
			pm, allow = m.effectivePolicyFromBoot()
		}
	} else {
		pm, allow = m.effectivePolicyFromBoot()
	}

	// Build egress manager config
	enforce := pm != Unrestricted
	mgrCfg := Config{
		Namespace:      m.cfg.ContainerNS,
		OpsNetns:       m.cfg.OpsNetns,
		IfName:         m.cfg.IfName,
		IfIPv4:         m.cfg.IfIPv4,
		IfIPv6:         m.cfg.IfIPv6,
		DnsListenPort:  m.cfg.DnsPort,
		Allowlist:      allow,
		StaticHosts:    map[string][]string{},
		WorkDir:        "/tmp/sprite-policy",
		TableName:      m.cfg.TableName,
		SetV4:          m.cfg.SetV4,
		SetV6:          m.cfg.SetV6,
		TimeoutSeconds: 300,
		EnableIPv6:     m.cfg.EnableIPv6,
		Enforce:        enforce,
	}
	// Start or update
	if m.egress == nil {
		eg, err := NewEgressPolicyManager(mgrCfg)
		if err != nil {
			return err
		}
		if err := eg.Start(ctx); err != nil {
			return err
		}
		m.egress = eg
		return nil
	}
	// Atomic reload: update allowlist and nftables rules without restarting DNS
	// 1. Update DNS allowlist (hot reload, no downtime)
	if err := m.egress.UpdateAllowlist(ctx, allow); err != nil {
		return fmt.Errorf("update allowlist: %w", err)
	}
	// 2. Reapply nftables rules atomically (preserves dynamic sets)
	if err := applyNftables(ctx, mgrCfg); err != nil {
		return fmt.Errorf("reapply nftables: %w", err)
	}
	tap.Logger(ctx).With("component", "policy").Info("policy reloaded atomically", "mode", pm, "domains", len(allow))
	return nil
}

// watcher implemented in config_watcher.go
