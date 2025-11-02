package policy

import (
	"context"
	"fmt"
	"net"
	"os"
	"strings"
	"sync"
	"time"

	"github.com/google/nftables"
	"github.com/miekg/dns"
	"github.com/superfly/sprite-env/pkg/tap"
)

// DNSServer implements a custom DNS server that forwards queries to upstream
// and writes allowed IPs to nftables sets.
type DNSServer struct {
	rules      []Rule // ordered rules for evaluation
	upstream   []string // parsed from resolv.conf
	table      string
	setV4      string
	setV6      string
	opsNetns   string
	nftConn    *nftables.Conn        // Netlink connection for nftables
	nftTable   *nftables.Table       // Reference to nftables table
	nftSetV4   *nftables.Set         // Reference to IPv4 set
	nftSetV6   *nftables.Set         // Reference to IPv6 set
	mu         sync.RWMutex
	nftMu      sync.Mutex // Serializes nftables updates to prevent race conditions
	servers    []*dns.Server // multiple servers for IPv4/IPv6
	ctx        context.Context
	cancel     context.CancelFunc
}

// NewDNSServer creates a new DNS server instance.
func NewDNSServer(ctx context.Context, rules []Rule, table, setV4, setV6, opsNetns string) (*DNSServer, error) {
	// Parse upstream DNS servers from /etc/resolv.conf
	upstream, err := parseResolvConf("/etc/resolv.conf")
	if err != nil {
		return nil, fmt.Errorf("parse resolv.conf: %w", err)
	}

	serverCtx, cancel := context.WithCancel(ctx)

	return &DNSServer{
		rules:    rules,
		upstream: upstream,
		table:    table,
		setV4:    setV4,
		setV6:    setV6,
		opsNetns: opsNetns,
		// nftables connection is lazy-initialized on first use
		ctx:    serverCtx,
		cancel: cancel,
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
	// Forward to upstream (no caching)
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

	// Check if domain is allowed before processing response
	if len(r.Question) > 0 && len(s.rules) > 0 {
		domain := strings.ToLower(strings.TrimSuffix(r.Question[0].Name, "."))
		if !s.isAllowed(domain) {
			// Domain is denied - return REFUSED
			tap.Logger(s.ctx).With("component", "policy", "proc", "dns").Warn("domain denied by policy", "domain", domain)
			m := new(dns.Msg)
			m.SetRcode(r, dns.RcodeRefused)
			w.WriteMsg(m)
			return
		}
	}

	// Preserve the original query ID from the client's request
	// The upstream response has its own ID which won't match the client's expectation
	response.Id = r.Id

	// Write allowed IPs to nftables (skip in unrestricted mode)
	if len(r.Question) > 0 && len(s.rules) > 0 {
		// Write IPs to nftables BEFORE returning response to prevent race condition
		// This ensures the nftables rule exists before the client gets the DNS response
		if err := s.writeIPsToNftables(response); err != nil {
			tap.Logger(s.ctx).With("component", "policy", "proc", "dns").Error("failed to write IPs to nftables", "error", err)
			// Continue anyway - don't block DNS response
		}
	}

	// Return response to client (after nftables rules are written)
	w.WriteMsg(response)
}

// isAllowed checks if a domain is allowed by evaluating rules.
// If no rules exist (unrestricted mode), allow everything.
// Otherwise, most specific matching rule wins (exact > subdomain wildcard > wildcard all).
func (s *DNSServer) isAllowed(domain string) bool {
	s.mu.RLock()
	defer s.mu.RUnlock()

	domain = strings.ToLower(strings.TrimSpace(domain))

	// If no rules, allow everything (unrestricted mode)
	if len(s.rules) == 0 {
		return true
	}

	// Evaluate rules by specificity: exact matches first, then wildcards
	// This allows "allow *, deny pornhub.com" to work intuitively

	// 1. Check for exact domain match (most specific)
	for _, rule := range s.rules {
		if rule.Domain == domain {
			return rule.Action == "allow"
		}
	}

	// 2. Check for subdomain wildcard match (*.example.com)
	for _, rule := range s.rules {
		if strings.HasPrefix(rule.Domain, "*.") {
			if MatchesPattern(domain, rule.Domain) {
				return rule.Action == "allow"
			}
		}
	}

	// 3. Check for wildcard all (*) (least specific)
	for _, rule := range s.rules {
		if rule.Domain == "*" {
			return rule.Action == "allow"
		}
	}

	// Default deny if no rule matches
	return false
}

// writeIPsToNftables writes IP addresses from DNS response to nftables sets.
// IPs are added with a fixed timeout and automatically refreshed on repeated queries.
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

	// Write IPv4 addresses to nftables with fixed timeout
	if len(v4IPs) > 0 {
		if err := s.addToNftablesSet(s.setV4, v4IPs); err != nil {
			return fmt.Errorf("failed to add IPv4 IPs to nftables: %w", err)
		}
	}

	// Write IPv6 addresses to nftables with fixed timeout
	if len(v6IPs) > 0 {
		if err := s.addToNftablesSet(s.setV6, v6IPs); err != nil {
			return fmt.Errorf("failed to add IPv6 IPs to nftables: %w", err)
		}
	}

	return nil
}

// ensureNftablesConnection initializes the nftables netlink connection if not already done.
func (s *DNSServer) ensureNftablesConnection() error {
	if s.nftConn != nil {
		return nil // Already initialized
	}

	// Create netlink connection for nftables
	// Note: OpsNetns not supported with netlink - only used in tests
	nftConn, err := nftables.New()
	if err != nil {
		return fmt.Errorf("create nftables connection: %w", err)
	}

	// Look up the nftables table
	nftTable := &nftables.Table{
		Name:   s.table,
		Family: nftables.TableFamilyINet,
	}

	// Get references to the sets
	sets, err := nftConn.GetSets(nftTable)
	if err != nil {
		return fmt.Errorf("get nftables sets: %w", err)
	}

	var nftSetV4, nftSetV6 *nftables.Set
	for _, set := range sets {
		if set.Name == s.setV4 {
			nftSetV4 = set
		}
		if set.Name == s.setV6 {
			nftSetV6 = set
		}
	}

	if nftSetV4 == nil {
		return fmt.Errorf("nftables set %s not found", s.setV4)
	}
	if nftSetV6 == nil {
		return fmt.Errorf("nftables set %s not found", s.setV6)
	}

	// Store references
	s.nftConn = nftConn
	s.nftTable = nftTable
	s.nftSetV4 = nftSetV4
	s.nftSetV6 = nftSetV6

	return nil
}

// addToNftablesSet adds IP addresses to an nftables set using netlink API.
// Much faster than exec-based approach (microseconds vs 50-200ms).
// IPs are added with a fixed 5-minute timeout. Re-adding existing IPs refreshes their timeout.
func (s *DNSServer) addToNftablesSet(setName string, ips []string) error {
	if len(ips) == 0 {
		return nil
	}

	// Serialize nftables updates to prevent concurrent conflicts
	s.nftMu.Lock()
	defer s.nftMu.Unlock()

	// Lazy-initialize nftables connection
	if err := s.ensureNftablesConnection(); err != nil {
		return fmt.Errorf("ensure nftables connection: %w", err)
	}

	// Select the correct set
	var targetSet *nftables.Set
	if setName == s.setV4 {
		targetSet = s.nftSetV4
	} else if setName == s.setV6 {
		targetSet = s.nftSetV6
	} else {
		return fmt.Errorf("unknown set name: %s", setName)
	}

	// Convert IPs to nftables set elements
	// Use fixed 5-minute timeout; re-adding refreshes the timeout automatically
	elements := make([]nftables.SetElement, 0, len(ips))
	for _, ipStr := range ips {
		ip := net.ParseIP(ipStr)
		if ip == nil {
			tap.Logger(s.ctx).With("component", "policy", "proc", "dns").Warn("invalid IP address", "ip", ipStr)
			continue
		}

		// Convert IP to key format
		var key []byte
		if setName == s.setV4 {
			// IPv4: use 4-byte representation
			ip4 := ip.To4()
			if ip4 == nil {
				tap.Logger(s.ctx).With("component", "policy", "proc", "dns").Warn("not an IPv4 address", "ip", ipStr)
				continue
			}
			key = []byte(ip4)
		} else {
			// IPv6: use 16-byte representation
			ip6 := ip.To16()
			if ip6 == nil {
				tap.Logger(s.ctx).With("component", "policy", "proc", "dns").Warn("not an IPv6 address", "ip", ipStr)
				continue
			}
			key = []byte(ip6)
		}

		// Use fixed 1-hour timeout (matches set default)
		// nftables automatically refreshes timeout when same IP is re-added
		elements = append(elements, nftables.SetElement{
			Key:     key,
			Timeout: 1 * time.Hour,
		})
	}

	if len(elements) == 0 {
		return nil
	}

	// Add elements to set via netlink (batched operation)
	if err := s.nftConn.SetAddElements(targetSet, elements); err != nil {
		tap.Logger(s.ctx).With("component", "policy", "proc", "dns").Warn("failed to add IPs to nftables", "set", setName, "error", err)
		return err
	}

	// Flush the netlink batch (commit changes)
	if err := s.nftConn.Flush(); err != nil {
		tap.Logger(s.ctx).With("component", "policy", "proc", "dns").Warn("failed to flush nftables changes", "set", setName, "error", err)
		return err
	}

	tap.Logger(s.ctx).With("component", "policy", "proc", "dns").Debug("added IPs to nftables via netlink", "set", setName, "count", len(elements))
	return nil
}

// UpdateAllowlist updates the rules.
func (s *DNSServer) UpdateAllowlist(rules []Rule) {
	s.mu.Lock()
	defer s.mu.Unlock()
	s.rules = rules
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
