package api

import (
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net"
	"net/url"
	"sync"
	"time"

	gorillaws "github.com/gorilla/websocket"
)

// ServeProxyWS implements the proxy tunnel over a WS-like connection.
// It accepts optional host/port in args. If not provided, it expects the first
// text frame to contain a JSON-encoded ProxyInitMessage.
func (h *Handlers) ServeProxyWS(ctx context.Context, ws WSLike, args url.Values) error {
	startTime := time.Now()
	proxyID := fmt.Sprintf("proxy-%d", time.Now().UnixNano())

	// Parse host/port from args, if present
	host := args.Get("host")
	portStr := args.Get("port")
	var port int
	var haveTarget bool
	if host != "" && portStr != "" {
		if _, err := fmt.Sscanf(portStr, "%d", &port); err == nil {
			haveTarget = true
		}
	}

	// If target not provided in args, read first text frame as JSON init
	if !haveTarget {
		mt, data, err := ws.ReadMessage()
		if err != nil {
			return err
		}
		if mt != gorillaws.TextMessage {
			// Try to close politely
			_ = ws.WriteMessage(gorillaws.CloseMessage, gorillaws.FormatCloseMessage(gorillaws.CloseUnsupportedData, "Expected JSON initialization message"))
			return fmt.Errorf("expected text init frame, got type %d", mt)
		}
		var initMsg ProxyInitMessage
		if err := json.Unmarshal(data, &initMsg); err != nil {
			_ = ws.WriteMessage(gorillaws.CloseMessage, gorillaws.FormatCloseMessage(gorillaws.CloseUnsupportedData, "Invalid JSON in initialization message"))
			return err
		}
		if initMsg.Port < 1 || initMsg.Port > 65535 {
			_ = ws.WriteMessage(gorillaws.CloseMessage, gorillaws.FormatCloseMessage(gorillaws.CloseUnsupportedData, "Invalid port number"))
			return fmt.Errorf("invalid port: %d", initMsg.Port)
		}
		if initMsg.Host == "" {
			initMsg.Host = "localhost"
		}
		host = initMsg.Host
		port = initMsg.Port
	}

	// Map localhost variants to configured bridge if present
	targetHost := host
	if targetHost == "localhost" || targetHost == "127.0.0.1" {
		if h.proxyLocalhostIPv4 != "" {
			targetHost = h.proxyLocalhostIPv4
		}
	} else if targetHost == "::1" {
		if h.proxyLocalhostIPv6 != "" {
			targetHost = h.proxyLocalhostIPv6
		}
	}

	targetAddr := net.JoinHostPort(targetHost, fmt.Sprintf("%d", port))

	// Dial target
	targetConn, err := net.Dial("tcp", targetAddr)
	if err != nil {
		_ = ws.WriteMessage(gorillaws.CloseMessage, gorillaws.FormatCloseMessage(gorillaws.CloseInternalServerErr, fmt.Sprintf("Failed to connect to target: %v", err)))
		return err
	}
	defer targetConn.Close()

	// Send success JSON message
	successMsg := map[string]any{
		"status": "connected",
		"target": targetAddr,
	}
	if data, err := json.Marshal(successMsg); err == nil {
		_ = ws.WriteMessage(gorillaws.TextMessage, data)
	}

	// Bidirectional copy between websocket and TCP
	var wg sync.WaitGroup
	wg.Add(2)

	// WS -> TCP
	go func() {
		defer wg.Done()
		defer targetConn.Close()
		for {
			mt, data, err := ws.ReadMessage()
			if err != nil {
				return
			}
			if mt == gorillaws.BinaryMessage {
				if _, err := targetConn.Write(data); err != nil {
					return
				}
			}
		}
	}()

	// TCP -> WS
	go func() {
		defer wg.Done()
		buf := make([]byte, 32*1024)
		for {
			n, err := targetConn.Read(buf)
			if err != nil {
				if err != io.EOF {
					// best-effort close
					_ = ws.WriteMessage(gorillaws.CloseMessage, gorillaws.FormatCloseMessage(gorillaws.CloseGoingAway, "upstream closed"))
				}
				return
			}
			if err := ws.WriteMessage(gorillaws.BinaryMessage, buf[:n]); err != nil {
				return
			}
		}
	}()

	wg.Wait()

	// Best-effort enrichment if available
	if enricher := h.getContextEnricher(ctx); enricher != nil {
		endTime := time.Now()
		duration := endTime.Sub(startTime)
		extraData := map[string]any{
			"proxy_id":    proxyID,
			"target_host": host,
			"target_port": port,
			"target_addr": targetAddr,
		}
		enricher.RequestEnd(ctx, &RequestInfo{
			RequestID:   proxyID,
			Method:      "WS",
			Path:        "/proxy",
			StartTime:   startTime,
			EndTime:     endTime,
			DurationMS:  duration.Milliseconds(),
			StatusCode:  200,
			Error:       nil,
			RequestType: "proxy",
			ExtraData:   extraData,
		})
	}

	return nil
}
