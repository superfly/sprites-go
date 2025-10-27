package policy

import (
	"bytes"
	"context"
	"fmt"
	"os/exec"
	"strings"

	"github.com/superfly/sprite-env/pkg/tap"
)

func applyNftables(ctx context.Context, cfg Config) error {
	script := renderNftScript(cfg)
	var cmd *exec.Cmd
	if cfg.OpsNetns != "" {
		cmd = exec.Command("ip", "netns", "exec", cfg.OpsNetns, "nft", "-f", "-")
	} else {
		cmd = exec.Command("nft", "-f", "-")
	}
	cmd.Stdin = bytes.NewReader([]byte(script))

	out, err := cmd.CombinedOutput()
	if err != nil {
		tap.Logger(ctx).With("component", "policy", "proc", "nft").Error("nft apply failed", "error", err, "output", string(out))
		return fmt.Errorf("nft apply failed: %w: %s", err, string(out))
	}
	tap.Logger(ctx).With("component", "policy", "proc", "nft").Info("nftables rules applied")
	return nil
}

func deleteNftables(ctx context.Context, cfg Config) error {
	var cmd *exec.Cmd
	if cfg.OpsNetns != "" {
		cmd = exec.Command("ip", "netns", "exec", cfg.OpsNetns, "nft", "delete", "table", "inet", cfg.TableName)
	} else {
		cmd = exec.Command("nft", "delete", "table", "inet", cfg.TableName)
	}
	out, err := cmd.CombinedOutput()
	if err != nil {
		// non-fatal if not found
		if !strings.Contains(strings.ToLower(string(out)), "no such file or directory") {
			tap.Logger(ctx).With("component", "policy", "proc", "nft").Warn("nft delete table failed", "error", err, "output", string(out))
		}
	} else {
		tap.Logger(ctx).With("component", "policy", "proc", "nft").Info("nftables table deleted")
	}
	return nil
}

func renderNftScript(cfg Config) string {
	var b strings.Builder

	// Create/update table and define sets + chains
	// nftables will atomically replace chain definitions while preserving sets
	fmt.Fprintf(&b, "table inet %s {\n", cfg.TableName)

	// Define sets (will be created if missing, preserved if existing)
	fmt.Fprintf(&b, "    set %s { type ipv4_addr; flags dynamic,timeout; timeout %ds; }\n", cfg.SetV4, cfg.TimeoutSeconds)
	if cfg.EnableIPv6 && cfg.SetV6 != "" {
		fmt.Fprintf(&b, "    set %s { type ipv6_addr; flags dynamic,timeout; timeout %ds; }\n", cfg.SetV6, cfg.TimeoutSeconds)
	}

	// Input chain: accept by default; explicit accept for DNS traffic to configured IPs (defensive)
	fmt.Fprintf(&b, "    chain input { type filter hook input priority 0; policy accept; ")
	if cfg.IfIPv4 != nil {
		fmt.Fprintf(&b, " ip daddr %s udp dport 53 accept; ip daddr %s tcp dport 53 accept;", cfg.IfIPv4.String(), cfg.IfIPv4.String())
	}
	if cfg.EnableIPv6 && cfg.IfIPv6 != nil {
		fmt.Fprintf(&b, " ip6 daddr %s udp dport 53 accept; ip6 daddr %s tcp dport 53 accept;", cfg.IfIPv6.String(), cfg.IfIPv6.String())
	}
	fmt.Fprintf(&b, " }\n")

	// Output chain: allow host to send to container over this interface unimpeded
	fmt.Fprintf(&b, "    chain output { type filter hook output priority 0; policy accept; oifname \"%s\" accept; }\n", cfg.IfName)

	// Forward chain: scope enforcement ONLY to our interface; default policy accept by default
	fmt.Fprintf(&b, "    chain forward { type filter hook forward priority 0; policy accept; ")
	// Allow replies
	fmt.Fprintf(&b, " ct state established,related accept;")
	// Allow inbound from host into container over this interface (host source IP)
	if cfg.IfIPv4 != nil {
		fmt.Fprintf(&b, " oifname \"%s\" ip saddr %s accept;", cfg.IfName, cfg.IfIPv4.String())
	}
	if cfg.EnableIPv6 && cfg.IfIPv6 != nil {
		fmt.Fprintf(&b, " oifname \"%s\" ip6 saddr %s accept;", cfg.IfName, cfg.IfIPv6.String())
	}
	// Allow DNS queries from container to host-side DNS IP/port via this interface
	// This MUST come before private IP blocking rules
	if cfg.IfIPv4 != nil {
		fmt.Fprintf(&b, " iifname \"%s\" tcp dport 53 ip daddr %s accept;", cfg.IfName, cfg.IfIPv4.String())
		fmt.Fprintf(&b, " iifname \"%s\" udp dport 53 ip daddr %s accept;", cfg.IfName, cfg.IfIPv4.String())
	}
	if cfg.EnableIPv6 && cfg.IfIPv6 != nil {
		fmt.Fprintf(&b, " iifname \"%s\" tcp dport 53 ip6 daddr %s accept;", cfg.IfName, cfg.IfIPv6.String())
		fmt.Fprintf(&b, " iifname \"%s\" udp dport 53 ip6 daddr %s accept;", cfg.IfName, cfg.IfIPv6.String())
	}
	// Explicitly block private/reserved destinations regardless of allowlist
	// Note: DNS traffic to host IPs is allowed above, so this won't block DNS
	fmt.Fprintf(&b, " iifname \"%s\" ip daddr { 10.0.0.0/8, 172.16.0.0/12, 192.168.0.0/16, 100.64.0.0/10, 127.0.0.0/8, 169.254.0.0/16 } drop;", cfg.IfName)
	if cfg.EnableIPv6 {
		fmt.Fprintf(&b, " iifname \"%s\" ip6 daddr { fd00::/8, fe80::/10, ::1/128, ff00::/8 } drop;", cfg.IfName)
	}

	if cfg.Enforce {
		// Permit egress only to allowed sets and default drop on our interface
		fmt.Fprintf(&b, " iifname \"%s\" ip daddr @%s accept;", cfg.IfName, cfg.SetV4)
		if cfg.EnableIPv6 && cfg.SetV6 != "" {
			fmt.Fprintf(&b, " iifname \"%s\" ip6 daddr @%s accept;", cfg.IfName, cfg.SetV6)
		}
		// For disallowed traffic, actively reject so clients fail fast
		fmt.Fprintf(&b, " iifname \"%s\" counter ip protocol tcp reject with tcp reset;", cfg.IfName)
		fmt.Fprintf(&b, " iifname \"%s\" counter ip protocol udp reject with icmpx port-unreachable;", cfg.IfName)
		if cfg.EnableIPv6 {
			fmt.Fprintf(&b, " iifname \"%s\" counter ip6 nexthdr tcp reject with tcp reset;", cfg.IfName)
			fmt.Fprintf(&b, " iifname \"%s\" counter ip6 nexthdr udp reject with icmpx port-unreachable;", cfg.IfName)
		}
		fmt.Fprintf(&b, " iifname \"%s\" counter drop; }\n", cfg.IfName)
	} else {
		// Observe-only: no gating; leave policy accept and no final drop
		fmt.Fprintf(&b, " }\n")
	}

	fmt.Fprintf(&b, "}\n")
	return b.String()
}
