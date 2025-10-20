package api

import (
	"fmt"
	"net/http"
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
	_ = fmt.Sprintf("proxy-%d", time.Now().UnixNano())
	h.logger.Info("Received proxy request", "method", r.Method, "url", r.URL.String(), "remote_addr", r.RemoteAddr)

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

	// Delegate to shared core implementation
	_ = h.ServeProxyWS(r.Context(), conn, r.URL.Query())
}
