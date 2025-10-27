package policy

import (
	"context"
	"fmt"
	"net"
	"os"
	"os/exec"
	"strings"
	"sync"
	"time"

	"github.com/miekg/dns"
	"github.com/superfly/sprite-env/pkg/tap"
)

// DNSServer implements a custom DNS server that forwards queries to upstream
// and writes allowed IPs to nftables sets.
type DNSServer struct {
	allowlist map[string]bool // domain -> allowed
	cache     map[string]*cachedEntry
	upstream  []string // parsed from resolv.conf
	table     string
	setV4     string
	setV6     string
	opsNetns  string
	mu        sync.RWMutex
	servers   []*dns.Server // multiple servers for IPv4/IPv6
	ctx       context.Context
	cancel    context.CancelFunc
}

type cachedEntry struct {
	msg    *dns.Msg
	expiry time.Time
}

// NewDNSServer creates a new DNS server instance.
func NewDNSServer(ctx context.Context, allowlist []string, table, setV4, setV6, opsNetns string) (*DNSServer, error) {
	// Parse upstream DNS servers from /etc/resolv.conf
	upstream, err := parseResolvConf("/etc/resolv.conf")
	if err != nil {
		return nil, fmt.Errorf("parse resolv.conf: %w", err)
	}

	// Build allowlist map for O(1) lookups
	allowMap := make(map[string]bool)
	for _, domain := range allowlist {
		allowMap[strings.ToLower(domain)] = true
	}

	serverCtx, cancel := context.WithCancel(ctx)

	return &DNSServer{
		allowlist: allowMap,
		cache:     make(map[string]*cachedEntry),
		upstream:  upstream,
		table:     table,
		setV4:     setV4,
		setV6:     setV6,
		opsNetns:  opsNetns,
		ctx:       serverCtx,
		cancel:    cancel,
	}, nil
}

// parseResolvConf reads /etc/resolv.conf and extracts nameserver entries.
func parseResolvConf(path string) ([]string, error) {
	content, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}

	var servers []string
	lines := strings.Split(string(content), "\n")
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if strings.HasPrefix(line, "nameserver ") {
			server := strings.TrimSpace(strings.TrimPrefix(line, "nameserver "))
			if server != "" {
				servers = append(servers, server)
			}
		}
	}

	if len(servers) == 0 {
		// Fallback to public DNS servers
		servers = []string{"1.1.1.1", "8.8.8.8"}
	}

	return servers, nil
}

type listenConfig struct {
	addr string
	net  string
}

// Start starts the DNS server on the specified addresses.
func (s *DNSServer) Start(ctx context.Context, listenAddrs []string) error {
	logger := tap.Logger(ctx).With("component", "policy", "proc", "dns")
	logger.Info("starting DNS servers", "addrs", listenAddrs)

	// Build listen configs with appropriate network types
	var configs []listenConfig
	for _, addr := range listenAddrs {
		netType := "udp"
		if strings.HasPrefix(addr, "[") {
			netType = "udp6"
		}
		configs = append(configs, listenConfig{addr: addr, net: netType})
	}

	// Start a server for each config
	for i, cfg := range configs {
		server := &dns.Server{
			Addr:    cfg.addr,
			Net:     cfg.net,
			Handler: s,
		}
		s.servers = append(s.servers, server)

		// Start server in a goroutine
		go func(srv *dns.Server, serverAddr string, serverIndex int) {
			if err := srv.ListenAndServe(); err != nil {
				logger.Error("DNS server failed to start", "addr", serverAddr, "error", err)
				return
			}
		}(server, cfg.addr, i)
	}

	// Give server time to start
	time.Sleep(100 * time.Millisecond)

	logger.Info("DNS server started", "addrs", listenAddrs, "serverCount", len(s.servers))
	return nil
}

// ServeDNS implements the dns.Handler interface.
func (s *DNSServer) ServeDNS(w dns.ResponseWriter, r *dns.Msg) {
	// Check cache first
	cacheKey := s.cacheKey(r)
	s.mu.RLock()
	if entry, exists := s.cache[cacheKey]; exists && time.Now().Before(entry.expiry) {
		s.mu.RUnlock()
		w.WriteMsg(entry.msg)
		return
	}
	s.mu.RUnlock()

	// Forward to upstream
	upstream := s.upstream[0] // Use first upstream server
	client := &dns.Client{
		Net:     "udp",
		Timeout: 5 * time.Second,
	}

	response, _, err := client.Exchange(r, net.JoinHostPort(upstream, "53"))
	if err != nil {
		tap.Logger(s.ctx).With("component", "policy", "proc", "dns").Warn("upstream DNS query failed", "error", err)
		// Return SERVFAIL
		m := new(dns.Msg)
		m.SetRcode(r, dns.RcodeServerFailure)
		w.WriteMsg(m)
		return
	}

	// Check if this is an allowed domain and write IPs to nftables
	if len(r.Question) > 0 {
		domain := strings.ToLower(strings.TrimSuffix(r.Question[0].Name, "."))
		if s.isAllowed(domain) {
			// Write IPs to nftables BEFORE returning response to prevent race condition
			// This ensures the nftables rule exists before the client gets the DNS response
			if err := s.writeIPsToNftables(response); err != nil {
				tap.Logger(s.ctx).With("component", "policy", "proc", "dns").Error("failed to write IPs to nftables", "error", err)
				// Continue anyway - don't block DNS response
			}
		}
	}

	// Cache the response
	s.cacheResponse(cacheKey, response)

	// Return response to client (after nftables rules are written)
	w.WriteMsg(response)
}

// isAllowed checks if a domain is in the allowlist.
func (s *DNSServer) isAllowed(domain string) bool {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.allowlist[domain]
}

// writeIPsToNftables writes IP addresses from DNS response to nftables sets.
func (s *DNSServer) writeIPsToNftables(response *dns.Msg) error {
	if response == nil || response.Rcode != dns.RcodeSuccess {
		return nil
	}

	var v4IPs, v6IPs []string
	for _, rr := range response.Answer {
		switch rr := rr.(type) {
		case *dns.A:
			v4IPs = append(v4IPs, rr.A.String())
		case *dns.AAAA:
			v6IPs = append(v6IPs, rr.AAAA.String())
		}
	}

	// Write IPv4 addresses to nftables
	if len(v4IPs) > 0 {
		if err := s.addToNftablesSet(s.setV4, v4IPs); err != nil {
			return fmt.Errorf("failed to add IPv4 IPs to nftables: %w", err)
		}
	}

	// Write IPv6 addresses to nftables
	if len(v6IPs) > 0 {
		if err := s.addToNftablesSet(s.setV6, v6IPs); err != nil {
			return fmt.Errorf("failed to add IPv6 IPs to nftables: %w", err)
		}
	}

	return nil
}

// addToNftablesSet adds IP addresses to an nftables set.
func (s *DNSServer) addToNftablesSet(setName string, ips []string) error {
	if len(ips) == 0 {
		return nil
	}

	// Build nftables command
	cmd := []string{"nft", "add", "element", "inet", s.table, setName, "{" + strings.Join(ips, ", ") + "}"}

	// Execute in OpsNetns if specified
	var execCmd *exec.Cmd
	if s.opsNetns != "" {
		args := append([]string{"netns", "exec", s.opsNetns}, cmd...)
		execCmd = exec.CommandContext(s.ctx, "ip", args...)
	} else {
		execCmd = exec.CommandContext(s.ctx, cmd[0], cmd[1:]...)
	}

	if err := execCmd.Run(); err != nil {
		tap.Logger(s.ctx).With("component", "policy", "proc", "dns").Warn("failed to add IPs to nftables", "set", setName, "ips", ips, "error", err)
		return err
	}

	tap.Logger(s.ctx).With("component", "policy", "proc", "dns").Debug("added IPs to nftables", "set", setName, "ips", ips)
	return nil
}

// cacheKey creates a cache key for a DNS query.
func (s *DNSServer) cacheKey(r *dns.Msg) string {
	if len(r.Question) == 0 {
		return ""
	}
	q := r.Question[0]
	return fmt.Sprintf("%s:%d:%d", q.Name, q.Qtype, q.Qclass)
}

// cacheResponse caches a DNS response with TTL.
func (s *DNSServer) cacheResponse(key string, response *dns.Msg) {
	if key == "" || response == nil {
		return
	}

	// Find minimum TTL from response
	minTTL := uint32(300) // Default 5 minutes
	for _, rr := range response.Answer {
		if rr.Header().Ttl < minTTL {
			minTTL = rr.Header().Ttl
		}
	}

	s.mu.Lock()
	defer s.mu.Unlock()
	s.cache[key] = &cachedEntry{
		msg:    response.Copy(),
		expiry: time.Now().Add(time.Duration(minTTL) * time.Second),
	}
}

// UpdateAllowlist updates the allowlist and clears cache.
func (s *DNSServer) UpdateAllowlist(domains []string) {
	allowMap := make(map[string]bool)
	for _, domain := range domains {
		allowMap[strings.ToLower(domain)] = true
	}

	s.mu.Lock()
	defer s.mu.Unlock()
	s.allowlist = allowMap
	s.cache = make(map[string]*cachedEntry) // Clear cache
}

// Shutdown stops the DNS server.
func (s *DNSServer) Shutdown(ctx context.Context) error {
	for _, server := range s.servers {
		if server != nil {
			server.Shutdown()
		}
	}
	s.cancel()
	return nil
}
