package handlers

import (
	"fmt"
	"io"
	"net"
	"net/http"
	"strconv"
	"strings"
	"sync"
)

// HandleProxy handles HTTP CONNECT proxy requests
func (h *Handlers) HandleProxy(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodConnect {
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// Extract port from the host header (format: hostname:port)
	host := r.Host
	if host == "" {
		host = r.URL.Host
	}

	parts := strings.Split(host, ":")
	if len(parts) != 2 {
		http.Error(w, "Invalid host format, expected hostname:port", http.StatusBadRequest)
		return
	}

	port, err := strconv.Atoi(parts[1])
	if err != nil || port < 1 || port > 65535 {
		http.Error(w, "Invalid port number", http.StatusBadRequest)
		return
	}

	// Connect to localhost:port
	targetAddr := fmt.Sprintf("localhost:%d", port)
	targetConn, err := net.Dial("tcp", targetAddr)
	if err != nil {
		h.logger.Error("Failed to connect to target", "addr", targetAddr, "error", err)
		http.Error(w, fmt.Sprintf("Failed to connect to target: %v", err), http.StatusBadGateway)
		return
	}
	defer targetConn.Close()

	// Send 200 Connection Established response
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
		http.Error(w, err.Error(), http.StatusInternalServerError)
		return
	}
	defer clientConn.Close()

	// Send the 200 Connection Established response
	_, err = clientConn.Write([]byte("HTTP/1.1 200 Connection Established\r\n\r\n"))
	if err != nil {
		h.logger.Error("Failed to write response", "error", err)
		return
	}

	// Start bidirectional copy
	var wg sync.WaitGroup
	wg.Add(2)

	// Copy from client to target
	go func() {
		defer wg.Done()
		_, err := io.Copy(targetConn, clientConn)
		if err != nil && err != io.EOF {
			h.logger.Debug("Copy error (client to target)", "error", err)
		}
		targetConn.(*net.TCPConn).CloseWrite()
	}()

	// Copy from target to client
	go func() {
		defer wg.Done()
		_, err := io.Copy(clientConn, targetConn)
		if err != nil && err != io.EOF {
			h.logger.Debug("Copy error (target to client)", "error", err)
		}
		clientConn.(*net.TCPConn).CloseWrite()
	}()

	wg.Wait()
	h.logger.Debug("Proxy connection closed", "target", targetAddr)
}
