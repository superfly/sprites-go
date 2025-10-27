package policy

import (
	"context"
	"fmt"
	"net"
	"os"
	"path/filepath"
	"sync"

	"github.com/superfly/sprite-env/pkg/tap"
)

// EgressPolicyManager defines lifecycle and update API for domain-based egress control.
type EgressPolicyManager interface {
	Start(ctx context.Context) error
	UpdateAllowlist(ctx context.Context, domains []string) error
	Stop(ctx context.Context) error
}

// Config configures the egress policy manager.
type Config struct {
	// Namespace is the Linux netns name for the sprite container (e.g., "sprite").
	Namespace string

	// OpsNetns, if set, is the netns name where host-side operations
	// (nftables and dnsmasq) are executed. This allows tests to fully
	// isolate changes from the real host namespace.
	OpsNetns string

	// IfName is the host-side veth interface name connected to the container.
	IfName string

	// IfIPv4 is the host-side IPv4 address (e.g., 10.10.0.1).
	IfIPv4 net.IP

	// IfIPv6 is the host-side IPv6 address (e.g., fd00::1). Optional.
	IfIPv6 net.IP

	// DnsListenPort is the dnsmasq listening port (usually 53).
	DnsListenPort int

	// Allowlist is the initial domain allowlist (wildcards like *.example.com supported via dnsmasq patterns).
	Allowlist []string

	// StaticHosts maps hostnames to one or more literal IPs. Primarily for tests.
	// These are rendered to dnsmasq address= lines (A/AAAA) in addition to nftset rules.
	StaticHosts map[string][]string

	// WorkDir is a base directory for generated config and state (per-instance subdir is created under this).
	WorkDir string

	// TableName is the nftables table name (inet family). Should be unique per instance.
	TableName string

	// SetV4 and SetV6 are nftables set names for dynamic IPv4/IPv6 destinations.
	SetV4 string
	SetV6 string

	// TimeoutSeconds controls nftables dynamic set entry timeout (also used when emitting dnsmasq nftset rules).
	TimeoutSeconds int

	// EnableIPv6 toggles IPv6 support.
	EnableIPv6 bool

	// Enforce controls whether allowlist gating is enforced.
	// If false, rules are installed in observe-only mode (no gating),
	// but dnsmasq and the nft table still run.
	Enforce bool

	// DropPrivileges controls whether dnsmasq drops to sprite-net user.
	// Tests can disable this to allow nft set updates without CAP setup.
	DropPrivileges bool
}

type egressManager struct {
	cfg       Config
	mu        sync.Mutex
	started   bool
	workDir   string
	dnsServer *DNSServer
}

// NewEgressPolicyManager creates a new manager with the given config.
func NewEgressPolicyManager(cfg Config) (EgressPolicyManager, error) {
	if cfg.IfName == "" || cfg.TableName == "" || cfg.SetV4 == "" {
		return nil, fmt.Errorf("invalid config: IfName, TableName, SetV4 are required")
	}
	if cfg.DnsListenPort == 0 {
		cfg.DnsListenPort = 53
	}
	if cfg.TimeoutSeconds <= 0 {
		cfg.TimeoutSeconds = 300
	}
	if cfg.WorkDir == "" {
		cfg.WorkDir = "/tmp/sprite-policy"
	}
	if !cfg.EnableIPv6 {
		// leave as-is; no change
	}
	// Default to enforcement unless explicitly disabled
	if !cfg.Enforce {
		// already set by caller
	} else {
		cfg.Enforce = true
	}
	// Default to dropping privileges unless explicitly disabled
	if !cfg.DropPrivileges {
		// honor explicit false; no change
	} else {
		cfg.DropPrivileges = true
	}
	// If enforcement not explicitly requested, enable when there is an allowlist
	if !cfg.Enforce && len(cfg.Allowlist) > 0 {
		cfg.Enforce = true
	}

	m := &egressManager{cfg: cfg}
	return m, nil
}

func (m *egressManager) Start(ctx context.Context) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	if m.started {
		return fmt.Errorf("policy manager already started")
	}

	logger := tap.Logger(ctx).With("component", "policy", "table", m.cfg.TableName)

	// Prepare work directory
	instanceDir := filepath.Join(m.cfg.WorkDir, fmt.Sprintf("%s", m.cfg.TableName))
	if err := os.MkdirAll(instanceDir, 0755); err != nil {
		return fmt.Errorf("creating work dir: %w", err)
	}
	m.workDir = instanceDir

	// Apply nftables ruleset
	if err := applyNftables(ctx, m.cfg); err != nil {
		return err
	}

	// Create and start DNS server
	dnsServer, err := NewDNSServer(ctx, m.cfg.Allowlist, m.cfg.TableName, m.cfg.SetV4, m.cfg.SetV6, m.cfg.OpsNetns)
	if err != nil {
		// Best effort cleanup nft if DNS server fails
		_ = deleteNftables(ctx, m.cfg)
		return fmt.Errorf("create DNS server: %w", err)
	}

	// Build listen addresses
	var listenAddrs []string
	if m.cfg.IfIPv4 != nil {
		addr := net.JoinHostPort(m.cfg.IfIPv4.String(), fmt.Sprintf("%d", m.cfg.DnsListenPort))
		listenAddrs = append(listenAddrs, addr)
	}
	if m.cfg.EnableIPv6 && m.cfg.IfIPv6 != nil {
		// For IPv6, we need to use square brackets format for miekg/dns
		addr := fmt.Sprintf("[%s]:%d", m.cfg.IfIPv6.String(), m.cfg.DnsListenPort)
		listenAddrs = append(listenAddrs, addr)
	}

	if err := dnsServer.Start(ctx, listenAddrs); err != nil {
		// Best effort cleanup nft if DNS server fails
		_ = deleteNftables(ctx, m.cfg)
		return fmt.Errorf("start DNS server: %w", err)
	}
	m.dnsServer = dnsServer

	logger.Info("egress policy started",
		"ifName", m.cfg.IfName,
		"dnsPort", m.cfg.DnsListenPort,
		"enableIPv6", m.cfg.EnableIPv6,
	)

	m.started = true
	return nil
}

func (m *egressManager) UpdateAllowlist(ctx context.Context, domains []string) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	if !m.started {
		return fmt.Errorf("policy manager not started")
	}

	// Update DNS server allowlist
	m.dnsServer.UpdateAllowlist(domains)

	tap.Logger(ctx).With("component", "policy").Info("allowlist updated", "count", len(domains))
	return nil
}

func (m *egressManager) Stop(ctx context.Context) error {
	m.mu.Lock()
	defer m.mu.Unlock()
	if !m.started {
		return nil
	}

	// Stop DNS server first
	if m.dnsServer != nil {
		if err := m.dnsServer.Shutdown(ctx); err != nil {
			tap.Logger(ctx).With("component", "policy").Warn("failed stopping DNS server", "error", err)
		}
	}
	// Remove nftables table
	if err := deleteNftables(ctx, m.cfg); err != nil {
		tap.Logger(ctx).With("component", "policy").Warn("failed deleting nftables table", "error", err)
	}

	m.started = false
	return nil
}
