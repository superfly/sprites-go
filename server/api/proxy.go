package api

import (
	"encoding/json"
	"fmt"
	"io"
	"net"
	"net/http"
	"sync"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

// ProxyInitMessage represents the initial message sent by the client to specify the target
type ProxyInitMessage struct {
	Host string `json:"host"`
	Port int    `json:"port"`
}

// HandleProxy handles WebSocket proxy requests
func (h *Handlers) HandleProxy(w http.ResponseWriter, r *http.Request) {
	startTime := time.Now()
	proxyID := fmt.Sprintf("proxy-%d", time.Now().UnixNano())
	h.logger.Info("Received proxy request", "method", r.Method, "url", r.URL.String(), "remote_addr", r.RemoteAddr, "proxy_id", proxyID)

	// Only allow GET for WebSocket upgrade
	if r.Method != http.MethodGet {
		h.logger.Warn("Non-GET method received", "method", r.Method)
		http.Error(w, "Method not allowed", http.StatusMethodNotAllowed)
		return
	}

	// Set up WebSocket upgrader
	upgrader := gorillaws.Upgrader{
		ReadBufferSize:  1024 * 1024, // 1MB buffer
		WriteBufferSize: 1024 * 1024, // 1MB buffer
		CheckOrigin: func(r *http.Request) bool {
			// Allow all origins for now
			// TODO: Add proper origin checking if needed
			return true
		},
	}

	// Upgrade to WebSocket
	conn, err := upgrader.Upgrade(w, r, nil)
	if err != nil {
		h.logger.Error("Failed to upgrade to WebSocket", "error", err)
		return
	}
	defer conn.Close()

	// Set read limit to allow reasonable message sizes
	conn.SetReadLimit(1024)

	h.logger.Debug("WebSocket upgrade successful")

	// Read initial message with target host:port
	messageType, data, err := conn.ReadMessage()
	if err != nil {
		h.logger.Error("Failed to read initial message", "error", err)
		return
	}

	if messageType != gorillaws.TextMessage {
		h.logger.Error("Expected text message for initialization", "messageType", messageType)
		conn.WriteMessage(gorillaws.CloseMessage,
			gorillaws.FormatCloseMessage(gorillaws.CloseUnsupportedData, "Expected JSON initialization message"))
		return
	}

	// Parse target from JSON message
	var initMsg ProxyInitMessage
	if err := json.Unmarshal(data, &initMsg); err != nil {
		h.logger.Error("Failed to parse initialization message", "error", err)
		conn.WriteMessage(gorillaws.CloseMessage,
			gorillaws.FormatCloseMessage(gorillaws.CloseUnsupportedData, "Invalid JSON in initialization message"))
		return
	}

	// Validate port range
	if initMsg.Port < 1 || initMsg.Port > 65535 {
		h.logger.Error("Invalid port number", "port", initMsg.Port)
		conn.WriteMessage(gorillaws.CloseMessage,
			gorillaws.FormatCloseMessage(gorillaws.CloseUnsupportedData, "Invalid port number"))
		return
	}

	// Default host to localhost if empty
	if initMsg.Host == "" {
		initMsg.Host = "localhost"
	}

	// When in container namespace, use configured bridge IP instead of localhost
	// This allows access to services running on localhost inside the container
	targetHost := initMsg.Host
	if targetHost == "localhost" || targetHost == "127.0.0.1" {
		// Use configured IPv4 bridge address for localhost connections
		if h.proxyLocalhostIPv4 != "" {
			targetHost = h.proxyLocalhostIPv4
		}
	} else if targetHost == "::1" {
		// Use configured IPv6 bridge address for IPv6 localhost
		if h.proxyLocalhostIPv6 != "" {
			targetHost = h.proxyLocalhostIPv6
		}
	}

	// Connect to target - use net.JoinHostPort for proper IPv6 handling
	targetAddr := net.JoinHostPort(targetHost, fmt.Sprintf("%d", initMsg.Port))
	h.logger.Info("Attempting to connect to target", "target", targetAddr, "original_host", initMsg.Host)

	targetConn, err := net.Dial("tcp", targetAddr)
	if err != nil {
		h.logger.Error("Failed to connect to target", "addr", targetAddr, "error", err)
		conn.WriteMessage(gorillaws.CloseMessage,
			gorillaws.FormatCloseMessage(gorillaws.CloseInternalServerErr, fmt.Sprintf("Failed to connect to target: %v", err)))
		return
	}
	defer targetConn.Close()

	h.logger.Info("Successfully connected to target", "target", targetAddr)

	// Send success response
	successMsg := map[string]interface{}{
		"status": "connected",
		"target": targetAddr,
	}
	successData, _ := json.Marshal(successMsg)
	if err := conn.WriteMessage(gorillaws.TextMessage, successData); err != nil {
		h.logger.Error("Failed to send success message", "error", err)
		return
	}

	// Remove read limit for data forwarding
	conn.SetReadLimit(10 * 1024 * 1024) // 10MB for large data transfers

	h.logger.Info("Proxy tunnel established", "target", targetAddr, "client", conn.RemoteAddr())

	// Start bidirectional data forwarding
	var wg sync.WaitGroup
	wg.Add(2)

	// Copy from WebSocket to target
	go func() {
		defer wg.Done()
		defer targetConn.Close()

		for {
			messageType, data, err := conn.ReadMessage()
			if err != nil {
				if !gorillaws.IsCloseError(err, gorillaws.CloseNormalClosure, gorillaws.CloseGoingAway) {
					h.logger.Debug("WebSocket read error (client to target)", "error", err)
				}
				return
			}

			// Only forward binary messages as data
			if messageType == gorillaws.BinaryMessage {
				_, err := targetConn.Write(data)
				if err != nil {
					h.logger.Debug("TCP write error (client to target)", "error", err)
					return
				}
			}
		}
	}()

	// Copy from target to WebSocket
	go func() {
		defer wg.Done()
		defer conn.Close()

		buffer := make([]byte, 32*1024) // 32KB buffer
		for {
			n, err := targetConn.Read(buffer)
			if err != nil {
				if err != io.EOF {
					h.logger.Debug("TCP read error (target to client)", "error", err)
				}
				return
			}

			err = conn.WriteMessage(gorillaws.BinaryMessage, buffer[:n])
			if err != nil {
				h.logger.Debug("WebSocket write error (target to client)", "error", err)
				return
			}
		}
	}()

	wg.Wait()
	endTime := time.Now()
	duration := time.Since(startTime)
	h.logger.Debug("Proxy connection closed", "target", targetAddr, "duration_ms", duration.Milliseconds())

	// Send notification to admin channel if available
	if enricher := h.getContextEnricher(r.Context()); enricher != nil {
		extraData := map[string]interface{}{
			"proxy_id":    proxyID,
			"target_host": initMsg.Host,
			"target_port": initMsg.Port,
			"target_addr": targetAddr,
		}
		enricher.RequestEnd(r.Context(), &RequestInfo{
			RequestID:   proxyID,
			Method:      r.Method,
			Path:        r.URL.Path,
			StartTime:   startTime,
			EndTime:     endTime,
			DurationMS:  duration.Milliseconds(),
			StatusCode:  200,
			Error:       nil,
			RequestType: "proxy",
			ExtraData:   extraData,
		})
	}
}
