package proxy

import (
	"fmt"
	"io"
	"log/slog"
	"net"
	"net/http"
	"strconv"
	"strings"
	"time"
)

// Handler handles CONNECT proxy requests
type Handler struct {
	logger *slog.Logger
}

// NewHandler creates a new proxy handler
func NewHandler(logger *slog.Logger) *Handler {
	return &Handler{
		logger: logger,
	}
}

// ServeHTTP handles CONNECT proxy requests
func (h *Handler) ServeHTTP(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodConnect {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// Parse the target host and port from the request
	host, portStr, err := net.SplitHostPort(r.Host)
	if err != nil {
		// If no port specified, try to parse as just port number
		if _, err := strconv.Atoi(r.Host); err == nil {
			portStr = r.Host
			host = "127.0.0.1"
		} else {
			http.Error(w, "Invalid target format", http.StatusBadRequest)
			return
		}
	}

	// Parse port number
	port, err := strconv.Atoi(portStr)
	if err != nil {
		http.Error(w, "Invalid port number", http.StatusBadRequest)
		return
	}

	if port < 1 || port > 65535 {
		http.Error(w, "Port number out of range", http.StatusBadRequest)
		return
	}

	// Always connect to localhost regardless of requested hostname
	targetAddr := fmt.Sprintf("127.0.0.1:%d", port)

	h.logger.Info("CONNECT proxy request",
		"requested_host", host,
		"target_port", port,
		"remote_addr", r.RemoteAddr,
	)

	// Establish connection to target
	targetConn, err := net.DialTimeout("tcp", targetAddr, 10*time.Second)
	if err != nil {
		h.logger.Error("Failed to connect to target",
			"error", err,
			"target_addr", targetAddr,
		)
		http.Error(w, fmt.Sprintf("Failed to connect to port %d", port), http.StatusServiceUnavailable)
		return
	}
	defer targetConn.Close()

	// Send 200 Connection Established
	w.WriteHeader(http.StatusOK)

	// Hijack the connection
	hijacker, ok := w.(http.Hijacker)
	if !ok {
		http.Error(w, "Hijacking not supported", http.StatusInternalServerError)
		return
	}

	clientConn, _, err := hijacker.Hijack()
	if err != nil {
		h.logger.Error("Failed to hijack connection", "error", err)
		return
	}
	defer clientConn.Close()

	// Start proxying data between client and target
	h.logger.Debug("Starting bidirectional copy",
		"client_addr", r.RemoteAddr,
		"target_addr", targetAddr,
	)

	// Copy data in both directions
	errc := make(chan error, 2)
	go func() {
		_, err := io.Copy(targetConn, clientConn)
		errc <- err
	}()
	go func() {
		_, err := io.Copy(clientConn, targetConn)
		errc <- err
	}()

	// Wait for either direction to finish
	err1 := <-errc
	err2 := <-errc

	if err1 != nil && !isClosedError(err1) {
		h.logger.Debug("Copy error from client to target", "error", err1)
	}
	if err2 != nil && !isClosedError(err2) {
		h.logger.Debug("Copy error from target to client", "error", err2)
	}

	h.logger.Debug("CONNECT proxy session ended",
		"client_addr", r.RemoteAddr,
		"target_addr", targetAddr,
	)
}

// isClosedError checks if an error is due to a closed connection
func isClosedError(err error) bool {
	if err == nil {
		return false
	}
	return strings.Contains(err.Error(), "use of closed network connection") ||
		err == io.EOF ||
		strings.Contains(err.Error(), "broken pipe")
}
