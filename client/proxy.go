package main

import (
	"crypto/tls"
	"fmt"
	"io"
	"net"
	"net/url"
	"os"
	"strconv"
	"strings"
	"sync"
)

func proxyCommand(baseURL, token string, args []string) {
	if len(args) == 0 {
		fmt.Fprintf(os.Stderr, "Error: proxy requires at least one port number\n")
		fmt.Fprintf(os.Stderr, "Usage: sprite-client proxy <port1> [port2] [port3] ...\n")
		os.Exit(1)
	}

	// Parse and validate ports
	ports := make([]int, 0, len(args))
	for _, arg := range args {
		port, err := strconv.Atoi(arg)
		if err != nil || port < 1 || port > 65535 {
			fmt.Fprintf(os.Stderr, "Error: Invalid port number: %s\n", arg)
			os.Exit(1)
		}
		ports = append(ports, port)
	}

	// Parse base URL to get proxy URL
	parsedURL, err := url.Parse(baseURL)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: Invalid base URL: %v\n", err)
		os.Exit(1)
	}

	// Create proxy URL
	proxyURL := fmt.Sprintf("%s://%s/proxy", parsedURL.Scheme, parsedURL.Host)

	fmt.Printf("Starting proxy for ports: %v\n", ports)
	fmt.Printf("Proxying through: %s\n", proxyURL)

	// Start listeners for each port
	var wg sync.WaitGroup
	for _, port := range ports {
		wg.Add(1)
		go func(port int) {
			defer wg.Done()
			if err := proxyPort(port, proxyURL, token); err != nil {
				fmt.Fprintf(os.Stderr, "Error on port %d: %v\n", port, err)
			}
		}(port)
	}

	wg.Wait()
}

func proxyPort(port int, proxyURL, token string) error {
	// Start local listener
	listener, err := net.Listen("tcp", fmt.Sprintf("localhost:%d", port))
	if err != nil {
		return fmt.Errorf("failed to listen: %w", err)
	}
	defer listener.Close()

	fmt.Printf("Listening on port %d...\n", port)

	for {
		// Accept local connection
		localConn, err := listener.Accept()
		if err != nil {
			debugLog("Failed to accept connection on port %d: %v", port, err)
			continue
		}

		// Handle connection in goroutine
		go handleProxyConnection(localConn, port, proxyURL, token)
	}
}

func handleProxyConnection(localConn net.Conn, port int, proxyURL, token string) {
	defer localConn.Close()

	// Parse proxy URL
	parsedURL, err := url.Parse(proxyURL)
	if err != nil {
		debugLog("Failed to parse proxy URL: %v", err)
		return
	}

	// Determine if we need TLS
	useTLS := parsedURL.Scheme == "https"
	host := parsedURL.Host

	// Connect to proxy server
	var proxyConn net.Conn
	if useTLS {
		tlsConfig := &tls.Config{
			InsecureSkipVerify: false, // Set to true if using self-signed certs
		}
		proxyConn, err = tls.Dial("tcp", host, tlsConfig)
	} else {
		proxyConn, err = net.Dial("tcp", host)
	}
	if err != nil {
		debugLog("Failed to connect to proxy: %v", err)
		return
	}
	defer proxyConn.Close()

	// Send CONNECT request
	connectReq := fmt.Sprintf("CONNECT localhost:%d HTTP/1.1\r\n", port)
	connectReq += fmt.Sprintf("Host: localhost:%d\r\n", port)
	connectReq += fmt.Sprintf("Authorization: Bearer %s\r\n", token)
	connectReq += "User-Agent: sprite-client/1.0\r\n"
	connectReq += "\r\n"

	_, err = proxyConn.Write([]byte(connectReq))
	if err != nil {
		debugLog("Failed to send CONNECT request: %v", err)
		return
	}

	// Read response
	response := make([]byte, 1024)
	n, err := proxyConn.Read(response)
	if err != nil {
		debugLog("Failed to read CONNECT response: %v", err)
		return
	}

	// Check if connection was established
	responseStr := string(response[:n])
	if !strings.Contains(responseStr, "200") {
		debugLog("CONNECT failed: %s", responseStr)
		return
	}

	debugLog("Proxy connection established for port %d", port)

	// Start bidirectional copy
	var wg sync.WaitGroup
	wg.Add(2)

	// Copy from local to proxy
	go func() {
		defer wg.Done()
		_, err := io.Copy(proxyConn, localConn)
		if err != nil && err != io.EOF {
			debugLog("Copy error (local to proxy): %v", err)
		}
		// Close write side of proxy connection
		if tcpConn, ok := proxyConn.(*net.TCPConn); ok {
			tcpConn.CloseWrite()
		} else if tlsConn, ok := proxyConn.(*tls.Conn); ok {
			// For TLS connections, we can't do half-close, so we'll rely on the other side
			_ = tlsConn
		}
	}()

	// Copy from proxy to local
	go func() {
		defer wg.Done()
		_, err := io.Copy(localConn, proxyConn)
		if err != nil && err != io.EOF {
			debugLog("Copy error (proxy to local): %v", err)
		}
		// Close write side of local connection
		if tcpConn, ok := localConn.(*net.TCPConn); ok {
			tcpConn.CloseWrite()
		}
	}()

	wg.Wait()
	debugLog("Proxy connection closed for port %d", port)
}
