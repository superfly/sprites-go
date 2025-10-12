package api

import (
	"context"
	"fmt"
	"log/slog"
	"net"
	"net/http"
	"net/http/httputil"
	"net/url"
	"strings"
	"time"
)

// ProxyHandler handles requests that should be proxied to another service
type ProxyHandler struct {
	ipv6Host       string
	ipv4Host       string
	targetPort     int
	ipv6Proxy      *httputil.ReverseProxy
	ipv4Proxy      *httputil.ReverseProxy
	logger         *slog.Logger
	preferredProxy *httputil.ReverseProxy
	preferredHost  string
}

// NewProxyHandler creates a new proxy handler that tries IPv6 first, then IPv4
func NewProxyHandler(logger *slog.Logger, ipv6Host string, ipv4Host string, targetPort int) *ProxyHandler {
	// Helper to create a proxy for a specific host
	createProxy := func(host string) *httputil.ReverseProxy {
		targetURL := &url.URL{
			Scheme: "http",
			Host:   fmt.Sprintf("%s:%d", host, targetPort),
		}

		director := func(req *http.Request) {
			req.URL.Scheme = targetURL.Scheme
			req.URL.Host = targetURL.Host
			req.Host = targetURL.Host

			// Remove the fly-replay-src header before proxying
			req.Header.Del("fly-replay-src")
		}

		return &httputil.ReverseProxy{
			Director: director,
			Transport: &http.Transport{
				MaxIdleConns:          100,
				IdleConnTimeout:       90 * time.Second,
				TLSHandshakeTimeout:   10 * time.Second,
				ExpectContinueTimeout: 1 * time.Second,
			},
			ErrorHandler: func(w http.ResponseWriter, r *http.Request, err error) {
				logger.Error("Proxy error",
					"error", err,
					"target", targetURL.String(),
					"path", r.URL.Path,
					"method", r.Method)
				http.Error(w, "Proxy error", http.StatusBadGateway)
			},
		}
	}

	return &ProxyHandler{
		ipv6Host:   ipv6Host,
		ipv4Host:   ipv4Host,
		targetPort: targetPort,
		ipv6Proxy:  createProxy(ipv6Host),
		ipv4Proxy:  createProxy(ipv4Host),
		logger:     logger,
	}
}

// testConnection attempts to connect to a host:port to verify it's reachable
func (p *ProxyHandler) testConnection(host string, port int) bool {
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Second)
	defer cancel()

	address := fmt.Sprintf("%s:%d", host, port)
	conn, err := (&net.Dialer{}).DialContext(ctx, "tcp", address)
	if err != nil {
		return false
	}
	conn.Close()
	return true
}

// selectProxy determines which proxy to use, testing both if needed
func (p *ProxyHandler) selectProxy() (*httputil.ReverseProxy, string) {
	// If we already have a preferred proxy, use it
	if p.preferredProxy != nil {
		return p.preferredProxy, p.preferredHost
	}

	// Try IPv6 first
	if p.testConnection(p.ipv6Host, p.targetPort) {
		p.logger.Info("Selected IPv6 for proxy", "host", p.ipv6Host)
		p.preferredProxy = p.ipv6Proxy
		p.preferredHost = p.ipv6Host
		return p.ipv6Proxy, p.ipv6Host
	}

	// Fall back to IPv4
	if p.testConnection(p.ipv4Host, p.targetPort) {
		p.logger.Info("Selected IPv4 for proxy", "host", p.ipv4Host)
		p.preferredProxy = p.ipv4Proxy
		p.preferredHost = p.ipv4Host
		return p.ipv4Proxy, p.ipv4Host
	}

	// Neither works, but we'll try IPv6 anyway (fail fast)
	p.logger.Warn("Neither IPv6 nor IPv4 connection test succeeded, defaulting to IPv6")
	p.preferredProxy = p.ipv6Proxy
	p.preferredHost = p.ipv6Host
	return p.ipv6Proxy, p.ipv6Host
}

// ServeHTTP handles the HTTP request by proxying it to the target
func (p *ProxyHandler) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	proxy, host := p.selectProxy()

	p.logger.Info("Proxying request",
		"hostname", r.Host,
		"method", r.Method,
		"path", r.URL.Path,
		"target", fmt.Sprintf("%s:%d", host, p.targetPort))

	proxy.ServeHTTP(w, r)
}

// ExtractProxyToken checks if the token has a proxy:: prefix and extracts the actual token
func ExtractProxyToken(token string) (actualToken string, isProxy bool) {
	const proxyPrefix = "proxy::"
	if strings.HasPrefix(token, proxyPrefix) {
		return strings.TrimPrefix(token, proxyPrefix), true
	}
	return token, false
}
