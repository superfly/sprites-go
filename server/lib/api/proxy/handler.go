package proxy

import (
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"net/http/httputil"
	"net/url"
	"strconv"
	"strings"
	"time"
)

// Handler handles proxy requests
type Handler struct {
	logger *slog.Logger
	client *http.Client
}

// NewHandler creates a new proxy handler
func NewHandler(logger *slog.Logger) *Handler {
	return &Handler{
		logger: logger,
		client: &http.Client{
			Timeout: 30 * time.Second,
			// Don't follow redirects automatically
			CheckRedirect: func(req *http.Request, via []*http.Request) error {
				return http.ErrUseLastResponse
			},
		},
	}
}

// ParseProxyTarget extracts the port from proxy state value
// Format: "proxy:<key>:<port>"
func ParseProxyTarget(stateValue string) (port int, err error) {
	parts := strings.SplitN(stateValue, ":", 3)
	if len(parts) != 3 {
		return 0, fmt.Errorf("invalid proxy format, expected 'proxy:key:port'")
	}

	if parts[0] != "proxy" {
		return 0, fmt.Errorf("not a proxy request")
	}

	port, err = strconv.Atoi(parts[2])
	if err != nil {
		return 0, fmt.Errorf("invalid port number: %v", err)
	}

	if port < 1 || port > 65535 {
		return 0, fmt.Errorf("port number out of range: %d", port)
	}

	return port, nil
}

// ServeHTTP handles proxy requests
func (h *Handler) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	// Get the proxy target from context (set by auth middleware)
	stateValue, ok := r.Context().Value("stateValue").(string)
	if !ok {
		http.Error(w, "Missing proxy configuration", http.StatusInternalServerError)
		return
	}

	port, err := ParseProxyTarget(stateValue)
	if err != nil {
		http.Error(w, fmt.Sprintf("Invalid proxy target: %v", err), http.StatusBadRequest)
		return
	}

	// Build target URL
	targetURL := &url.URL{
		Scheme: "http",
		Host:   fmt.Sprintf("127.0.0.1:%d", port),
	}

	// Log the proxy request
	h.logger.Info("Proxying request",
		"method", r.Method,
		"path", r.URL.Path,
		"target_port", port,
		"remote_addr", r.RemoteAddr,
	)

	// Create a reverse proxy
	proxy := httputil.NewSingleHostReverseProxy(targetURL)

	// Customize the proxy error handler
	proxy.ErrorHandler = func(w http.ResponseWriter, r *http.Request, err error) {
		h.logger.Error("Proxy error",
			"error", err,
			"target_port", port,
			"path", r.URL.Path,
		)

		// Check if we've already started writing the response
		if w.Header().Get("Content-Type") != "" {
			// Headers already sent, can't change status
			return
		}

		// Return appropriate error to client
		if err == io.EOF {
			http.Error(w, "Target service closed connection", http.StatusBadGateway)
		} else if strings.Contains(err.Error(), "connection refused") {
			http.Error(w, fmt.Sprintf("Target service on port %d is not available", port), http.StatusServiceUnavailable)
		} else if strings.Contains(err.Error(), "timeout") {
			http.Error(w, "Target service timeout", http.StatusGatewayTimeout)
		} else {
			http.Error(w, fmt.Sprintf("Proxy error: %v", err), http.StatusBadGateway)
		}
	}

	// Modify the request to ensure it goes to the right place
	proxy.Director = func(req *http.Request) {
		req.URL.Scheme = targetURL.Scheme
		req.URL.Host = targetURL.Host
		req.Host = targetURL.Host

		// Remove the fly-replay-src header so it doesn't confuse the target
		req.Header.Del("fly-replay-src")

		// Add X-Forwarded headers
		if clientIP, _, ok := strings.Cut(r.RemoteAddr, ":"); ok {
			req.Header.Set("X-Forwarded-For", clientIP)
		}
		req.Header.Set("X-Forwarded-Proto", "http")
		req.Header.Set("X-Forwarded-Host", r.Host)
	}

	// Perform the proxy request
	proxy.ServeHTTP(w, r)
}

// HealthCheck checks if a target port is responding
func (h *Handler) HealthCheck(port int) error {
	resp, err := h.client.Get(fmt.Sprintf("http://127.0.0.1:%d/health", port))
	if err != nil {
		return err
	}
	defer resp.Body.Close()

	if resp.StatusCode >= 500 {
		return fmt.Errorf("unhealthy status code: %d", resp.StatusCode)
	}

	return nil
}
