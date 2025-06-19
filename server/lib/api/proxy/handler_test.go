package proxy

import (
	"bufio"
	"fmt"
	"io"
	"log/slog"
	"net"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"
)

func TestProxyHandler_InvalidMethod(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	handler := NewHandler(logger)

	// Test non-CONNECT methods
	methods := []string{"GET", "POST", "PUT", "DELETE", "HEAD"}
	for _, method := range methods {
		t.Run(method, func(t *testing.T) {
			req := httptest.NewRequest(method, "http://example.com:8080", nil)
			rr := httptest.NewRecorder()
			handler.ServeHTTP(rr, req)

			if rr.Code != http.StatusMethodNotAllowed {
				t.Errorf("handler returned wrong status code for %s: got %v want %v", 
					method, rr.Code, http.StatusMethodNotAllowed)
			}
		})
	}
}

func TestProxyHandler_CONNECT(t *testing.T) {
	logger := slog.New(slog.NewTextHandler(io.Discard, nil))
	handler := NewHandler(logger)

	// Create a test backend TCP server
	backend, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatalf("Failed to create backend listener: %v", err)
	}
	defer backend.Close()

	backendPort := backend.Addr().(*net.TCPAddr).Port

	// Handle backend connections
	go func() {
		for {
			conn, err := backend.Accept()
			if err != nil {
				return
			}
			// Echo server - send back what we receive
			go func(c net.Conn) {
				defer c.Close()
				io.Copy(c, c)
			}(conn)
		}
	}()

	tests := []struct {
		name           string
		host           string
		expectedStatus int
		expectedError  string
	}{
		{
			name:           "valid CONNECT with hostname:port",
			host:           fmt.Sprintf("example.com:%d", backendPort),
			expectedStatus: http.StatusOK,
		},
		{
			name:           "valid CONNECT with just port",
			host:           fmt.Sprintf("%d", backendPort),
			expectedStatus: http.StatusOK,
		},
		{
			name:           "valid CONNECT with localhost",
			host:           fmt.Sprintf("localhost:%d", backendPort),
			expectedStatus: http.StatusOK,
		},
		{
			name:           "invalid port format",
			host:           "example.com:abc",
			expectedStatus: http.StatusBadRequest,
			expectedError:  "Invalid port number",
		},
		{
			name:           "port out of range",
			host:           "example.com:70000",
			expectedStatus: http.StatusBadRequest,
			expectedError:  "Port number out of range",
		},
		{
			name:           "connection refused",
			host:           "example.com:59999",
			expectedStatus: http.StatusServiceUnavailable,
			expectedError:  "Failed to connect to port 59999",
		},
		{
			name:           "missing port",
			host:           "example.com",
			expectedStatus: http.StatusBadRequest,
			expectedError:  "Invalid target format",
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Create a custom ResponseWriter that supports hijacking
			server := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
				r.Method = http.MethodConnect
				r.Host = tt.host
				handler.ServeHTTP(w, r)
			}))
			defer server.Close()

			// For successful CONNECT tests, we need to test the actual proxy functionality
			if tt.expectedStatus == http.StatusOK {
				// Make a request to the test server
				req, err := http.NewRequest("CONNECT", server.URL, nil)
				if err != nil {
					t.Fatalf("Failed to create request: %v", err)
				}
				req.Host = tt.host

				// Use raw TCP connection to test CONNECT
				conn, err := net.Dial("tcp", strings.TrimPrefix(server.URL, "http://"))
				if err != nil {
					t.Fatalf("Failed to connect: %v", err)
				}
				defer conn.Close()

				// Send CONNECT request
				fmt.Fprintf(conn, "CONNECT %s HTTP/1.1\r\nHost: %s\r\n\r\n", tt.host, tt.host)

				// Read response
				reader := bufio.NewReader(conn)
				resp, err := http.ReadResponse(reader, req)
				if err != nil {
					t.Fatalf("Failed to read response: %v", err)
				}

				if resp.StatusCode != tt.expectedStatus {
					t.Errorf("Got status %d, want %d", resp.StatusCode, tt.expectedStatus)
				}

				// For successful CONNECT, test the tunnel
				if resp.StatusCode == http.StatusOK {
					// Send test data through the tunnel
					testData := "Hello, proxy!"
					conn.Write([]byte(testData))

					// Read echoed data
					buf := make([]byte, len(testData))
					conn.SetReadDeadline(time.Now().Add(time.Second))
					n, err := conn.Read(buf)
					if err != nil {
						t.Errorf("Failed to read from tunnel: %v", err)
					}
					if string(buf[:n]) != testData {
						t.Errorf("Got %q, want %q", string(buf[:n]), testData)
					}
				}
			} else {
				// For error cases, just test the response
				req := httptest.NewRequest(http.MethodConnect, "/", nil)
				req.Host = tt.host
				rr := httptest.NewRecorder()
				handler.ServeHTTP(rr, req)

				if rr.Code != tt.expectedStatus {
					t.Errorf("handler returned wrong status code: got %v want %v", 
						rr.Code, tt.expectedStatus)
				}

				if tt.expectedError != "" && !strings.Contains(rr.Body.String(), tt.expectedError) {
					t.Errorf("handler returned unexpected error: got %v want containing %v", 
						rr.Body.String(), tt.expectedError)
				}
			}
		})
	}
}

func TestIsClosedError(t *testing.T) {
	tests := []struct {
		name     string
		err      error
		expected bool
	}{
		{
			name:     "nil error",
			err:      nil,
			expected: false,
		},
		{
			name:     "EOF error",
			err:      io.EOF,
			expected: true,
		},
		{
			name:     "closed connection error",
			err:      fmt.Errorf("use of closed network connection"),
			expected: true,
		},
		{
			name:     "broken pipe error",
			err:      fmt.Errorf("broken pipe"),
			expected: true,
		},
		{
			name:     "other error",
			err:      fmt.Errorf("some other error"),
			expected: false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			result := isClosedError(tt.err)
			if result != tt.expected {
				t.Errorf("isClosedError(%v) = %v, want %v", tt.err, result, tt.expected)
			}
		})
	}
}
