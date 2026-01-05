package sprites

import (
	"bufio"
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"time"
)

// ServiceStream represents a streaming service operation (start/stop/create)
type ServiceStream struct {
	reader  io.ReadCloser
	scanner *bufio.Scanner
	done    bool
}

// Next reads the next log event from the service stream
func (ss *ServiceStream) Next() (*ServiceLogEvent, error) {
	if ss.done {
		return nil, io.EOF
	}

	if !ss.scanner.Scan() {
		ss.done = true
		if err := ss.scanner.Err(); err != nil {
			return nil, err
		}
		return nil, io.EOF
	}

	line := ss.scanner.Text()
	if line == "" {
		// Skip empty lines
		return ss.Next()
	}

	var event ServiceLogEvent
	if err := json.Unmarshal([]byte(line), &event); err != nil {
		return nil, fmt.Errorf("failed to parse service log event: %w", err)
	}

	return &event, nil
}

// Close closes the service stream
func (ss *ServiceStream) Close() error {
	if ss.reader != nil {
		return ss.reader.Close()
	}
	return nil
}

// ProcessAll processes all messages in the service stream
func (ss *ServiceStream) ProcessAll(handler func(*ServiceLogEvent) error) error {
	defer ss.Close()

	for {
		event, err := ss.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}

		if err := handler(event); err != nil {
			return err
		}
	}

	return nil
}

// ListServices retrieves all services for a sprite
func (c *Client) ListServices(ctx context.Context, spriteName string) ([]*ServiceWithState, error) {
	url := fmt.Sprintf("%s/v1/sprites/%s/services", c.baseURL, spriteName)

	httpReq, err := http.NewRequestWithContext(ctx, "GET", url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))

	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("failed to make request: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	var services []*ServiceWithState
	if err := json.NewDecoder(resp.Body).Decode(&services); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	return services, nil
}

// ListServices retrieves all services for this sprite
func (s *Sprite) ListServices(ctx context.Context) ([]*ServiceWithState, error) {
	return s.client.ListServices(ctx, s.name)
}

// GetService retrieves a specific service
func (c *Client) GetService(ctx context.Context, spriteName, serviceName string) (*ServiceWithState, error) {
	url := fmt.Sprintf("%s/v1/sprites/%s/services/%s", c.baseURL, spriteName, serviceName)

	httpReq, err := http.NewRequestWithContext(ctx, "GET", url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))

	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("failed to make request: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode == http.StatusNotFound {
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("service not found: %s", string(body))
	}

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	var service ServiceWithState
	if err := json.NewDecoder(resp.Body).Decode(&service); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	return &service, nil
}

// GetService retrieves a specific service for this sprite
func (s *Sprite) GetService(ctx context.Context, serviceName string) (*ServiceWithState, error) {
	return s.client.GetService(ctx, s.name, serviceName)
}

// CreateService creates or updates a service and returns a stream of log events
func (c *Client) CreateService(ctx context.Context, spriteName, serviceName string, req *ServiceRequest) (*ServiceStream, error) {
	return c.CreateServiceWithDuration(ctx, spriteName, serviceName, req, 0)
}

// CreateServiceWithDuration creates a service with a custom monitoring duration
func (c *Client) CreateServiceWithDuration(ctx context.Context, spriteName, serviceName string, req *ServiceRequest, duration time.Duration) (*ServiceStream, error) {
	url := fmt.Sprintf("%s/v1/sprites/%s/services/%s", c.baseURL, spriteName, serviceName)
	if duration > 0 {
		url = fmt.Sprintf("%s?duration=%s", url, duration.String())
	}

	jsonData, err := json.Marshal(req)
	if err != nil {
		return nil, fmt.Errorf("failed to marshal request: %w", err)
	}

	httpReq, err := http.NewRequestWithContext(ctx, "PUT", url, bytes.NewReader(jsonData))
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))
	httpReq.Header.Set("Content-Type", "application/json")

	// Use client with no timeout for streaming
	streamClient := &http.Client{
		Transport: c.httpClient.Transport,
		Timeout:   0,
	}
	resp, err := streamClient.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("failed to make request: %w", err)
	}

	if resp.StatusCode == http.StatusConflict {
		body, _ := io.ReadAll(resp.Body)
		resp.Body.Close()
		return nil, fmt.Errorf("service conflict: %s", string(body))
	}

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		resp.Body.Close()
		return nil, fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	return &ServiceStream{
		reader:  resp.Body,
		scanner: bufio.NewScanner(resp.Body),
	}, nil
}

// CreateService creates a service for this sprite
func (s *Sprite) CreateService(ctx context.Context, serviceName string, req *ServiceRequest) (*ServiceStream, error) {
	return s.client.CreateService(ctx, s.name, serviceName, req)
}

// CreateServiceWithDuration creates a service with a custom monitoring duration
func (s *Sprite) CreateServiceWithDuration(ctx context.Context, serviceName string, req *ServiceRequest, duration time.Duration) (*ServiceStream, error) {
	return s.client.CreateServiceWithDuration(ctx, s.name, serviceName, req, duration)
}

// DeleteService deletes a service
func (c *Client) DeleteService(ctx context.Context, spriteName, serviceName string) error {
	url := fmt.Sprintf("%s/v1/sprites/%s/services/%s", c.baseURL, spriteName, serviceName)

	httpReq, err := http.NewRequestWithContext(ctx, "DELETE", url, nil)
	if err != nil {
		return fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))

	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		return fmt.Errorf("failed to make request: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode == http.StatusNotFound {
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("service not found: %s", string(body))
	}

	if resp.StatusCode == http.StatusConflict {
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("service conflict: %s", string(body))
	}

	if resp.StatusCode != http.StatusNoContent {
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	return nil
}

// DeleteService deletes a service for this sprite
func (s *Sprite) DeleteService(ctx context.Context, serviceName string) error {
	return s.client.DeleteService(ctx, s.name, serviceName)
}

// StartService starts a service and returns a stream of log events
func (c *Client) StartService(ctx context.Context, spriteName, serviceName string) (*ServiceStream, error) {
	return c.StartServiceWithDuration(ctx, spriteName, serviceName, 0)
}

// StartServiceWithDuration starts a service with a custom monitoring duration
func (c *Client) StartServiceWithDuration(ctx context.Context, spriteName, serviceName string, duration time.Duration) (*ServiceStream, error) {
	url := fmt.Sprintf("%s/v1/sprites/%s/services/%s/start", c.baseURL, spriteName, serviceName)
	if duration > 0 {
		url = fmt.Sprintf("%s?duration=%s", url, duration.String())
	}

	httpReq, err := http.NewRequestWithContext(ctx, "POST", url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))

	// Use client with no timeout for streaming
	streamClient := &http.Client{
		Transport: c.httpClient.Transport,
		Timeout:   0,
	}
	resp, err := streamClient.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("failed to make request: %w", err)
	}

	if resp.StatusCode == http.StatusNotFound {
		body, _ := io.ReadAll(resp.Body)
		resp.Body.Close()
		return nil, fmt.Errorf("service not found: %s", string(body))
	}

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		resp.Body.Close()
		return nil, fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	return &ServiceStream{
		reader:  resp.Body,
		scanner: bufio.NewScanner(resp.Body),
	}, nil
}

// StartService starts a service for this sprite
func (s *Sprite) StartService(ctx context.Context, serviceName string) (*ServiceStream, error) {
	return s.client.StartService(ctx, s.name, serviceName)
}

// StartServiceWithDuration starts a service with a custom monitoring duration
func (s *Sprite) StartServiceWithDuration(ctx context.Context, serviceName string, duration time.Duration) (*ServiceStream, error) {
	return s.client.StartServiceWithDuration(ctx, s.name, serviceName, duration)
}

// StopService stops a service and returns a stream of log events
func (c *Client) StopService(ctx context.Context, spriteName, serviceName string) (*ServiceStream, error) {
	return c.StopServiceWithTimeout(ctx, spriteName, serviceName, 0)
}

// StopServiceWithTimeout stops a service with a custom timeout
func (c *Client) StopServiceWithTimeout(ctx context.Context, spriteName, serviceName string, timeout time.Duration) (*ServiceStream, error) {
	url := fmt.Sprintf("%s/v1/sprites/%s/services/%s/stop", c.baseURL, spriteName, serviceName)
	if timeout > 0 {
		url = fmt.Sprintf("%s?timeout=%s", url, timeout.String())
	}

	httpReq, err := http.NewRequestWithContext(ctx, "POST", url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))

	// Use client with no timeout for streaming
	streamClient := &http.Client{
		Transport: c.httpClient.Transport,
		Timeout:   0,
	}
	resp, err := streamClient.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("failed to make request: %w", err)
	}

	if resp.StatusCode == http.StatusNotFound {
		body, _ := io.ReadAll(resp.Body)
		resp.Body.Close()
		return nil, fmt.Errorf("service not found: %s", string(body))
	}

	if resp.StatusCode == http.StatusConflict {
		body, _ := io.ReadAll(resp.Body)
		resp.Body.Close()
		return nil, fmt.Errorf("service not running: %s", string(body))
	}

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		resp.Body.Close()
		return nil, fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	return &ServiceStream{
		reader:  resp.Body,
		scanner: bufio.NewScanner(resp.Body),
	}, nil
}

// StopService stops a service for this sprite
func (s *Sprite) StopService(ctx context.Context, serviceName string) (*ServiceStream, error) {
	return s.client.StopService(ctx, s.name, serviceName)
}

// StopServiceWithTimeout stops a service with a custom timeout
func (s *Sprite) StopServiceWithTimeout(ctx context.Context, serviceName string, timeout time.Duration) (*ServiceStream, error) {
	return s.client.StopServiceWithTimeout(ctx, s.name, serviceName, timeout)
}

// SignalService sends a signal to a running service
func (c *Client) SignalService(ctx context.Context, spriteName, serviceName, signal string) error {
	url := fmt.Sprintf("%s/v1/sprites/%s/services/signal", c.baseURL, spriteName)

	reqBody := struct {
		Name   string `json:"name"`
		Signal string `json:"signal"`
	}{
		Name:   serviceName,
		Signal: signal,
	}

	jsonData, err := json.Marshal(reqBody)
	if err != nil {
		return fmt.Errorf("failed to marshal request: %w", err)
	}

	httpReq, err := http.NewRequestWithContext(ctx, "POST", url, bytes.NewReader(jsonData))
	if err != nil {
		return fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))
	httpReq.Header.Set("Content-Type", "application/json")

	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		return fmt.Errorf("failed to make request: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode == http.StatusNotFound {
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("service not found: %s", string(body))
	}

	if resp.StatusCode == http.StatusConflict {
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("service not running: %s", string(body))
	}

	if resp.StatusCode == http.StatusBadRequest {
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("invalid signal: %s", string(body))
	}

	if resp.StatusCode != http.StatusNoContent {
		body, _ := io.ReadAll(resp.Body)
		return fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	return nil
}

// SignalService sends a signal to a service for this sprite
func (s *Sprite) SignalService(ctx context.Context, serviceName, signal string) error {
	return s.client.SignalService(ctx, s.name, serviceName, signal)
}
