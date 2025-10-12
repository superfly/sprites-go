package api

import (
	"fmt"
	"log/slog"
	"net/http"
	"net/http/httputil"
	"net/url"
	"strings"
	"time"
)

// ProxyHandler handles requests that should be proxied to another service
type ProxyHandler struct {
	targetHost string
	targetPort int
	proxy      *httputil.ReverseProxy
	logger     *slog.Logger
}

// NewProxyHandler creates a new proxy handler
func NewProxyHandler(logger *slog.Logger, targetHost string, targetPort int) *ProxyHandler {
	targetURL := &url.URL{
		Scheme: "http",
		Host:   fmt.Sprintf("%s:%d", targetHost, targetPort),
	}

	// Create a custom director function
	director := func(req *http.Request) {
		req.URL.Scheme = targetURL.Scheme
		req.URL.Host = targetURL.Host
		req.Host = targetURL.Host

		// Remove the fly-replay-src header before proxying
		req.Header.Del("fly-replay-src")
	}

	// Create the reverse proxy with custom transport
	proxy := &httputil.ReverseProxy{
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

	return &ProxyHandler{
		targetHost: targetHost,
		targetPort: targetPort,
		proxy:      proxy,
		logger:     logger.With("hostname", fmt.Sprintf("%s:%d", targetHost, targetPort)),
	}
}

// ServeHTTP handles the HTTP request by proxying it to the target
func (p *ProxyHandler) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	p.logger.Info("Proxying request",
		"method", r.Method,
		"path", r.URL.Path,
		"target", fmt.Sprintf("%s:%d", p.targetHost, p.targetPort))

	p.proxy.ServeHTTP(w, r)
}

// ExtractProxyToken checks if the token has a proxy:: prefix and extracts the actual token
func ExtractProxyToken(token string) (actualToken string, isProxy bool) {
	const proxyPrefix = "proxy::"
	if strings.HasPrefix(token, proxyPrefix) {
		return strings.TrimPrefix(token, proxyPrefix), true
	}
	return token, false
}
