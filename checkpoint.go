package sprites

import (
	"bufio"
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"strings"
)

// CheckpointStream represents a streaming checkpoint operation
type CheckpointStream struct {
	reader  io.ReadCloser
	scanner *bufio.Scanner
	done    bool
}

// RestoreStream represents a streaming restore operation
type RestoreStream struct {
	reader  io.ReadCloser
	scanner *bufio.Scanner
	done    bool
}

// CreateCheckpointWithComment creates a new checkpoint for the sprite with an optional comment
func (c *Client) CreateCheckpointWithComment(ctx context.Context, spriteName string, comment string) (*CheckpointStream, error) {
	// Build URL
	url := fmt.Sprintf("%s/v1/sprites/%s/checkpoint", c.baseURL, spriteName)

    // Create request body (backward compatible if comment is empty)
    payload := map[string]interface{}{}
    if comment != "" {
        payload["comment"] = comment
    }
    jsonData, err := json.Marshal(payload)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	// Create HTTP request
	httpReq, err := http.NewRequestWithContext(ctx, "POST", url, bytes.NewReader(jsonData))
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))
	httpReq.Header.Set("Content-Type", "application/json")

	// Use client with no timeout for streaming, but preserve transport for socket support
	streamClient := &http.Client{
		Transport: c.httpClient.Transport,
		Timeout:   0,
	}
	resp, err := streamClient.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("failed to make request: %w", err)
	}

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		resp.Body.Close()
		return nil, fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	// Return streaming reader
	return &CheckpointStream{
		reader:  resp.Body,
		scanner: bufio.NewScanner(resp.Body),
	}, nil
}

// CreateCheckpoint creates a new checkpoint for the sprite (no comment)
func (c *Client) CreateCheckpoint(ctx context.Context, spriteName string) (*CheckpointStream, error) {
    return c.CreateCheckpointWithComment(ctx, spriteName, "")
}

// CreateCheckpoint creates a new checkpoint for this sprite (no comment)
func (s *Sprite) CreateCheckpoint(ctx context.Context) (*CheckpointStream, error) {
    return s.client.CreateCheckpointWithComment(ctx, s.name, "")
}

// CreateCheckpointWithComment creates a new checkpoint for this sprite with an optional comment
func (s *Sprite) CreateCheckpointWithComment(ctx context.Context, comment string) (*CheckpointStream, error) {
    return s.client.CreateCheckpointWithComment(ctx, s.name, comment)
}

// ListCheckpointsOptions contains options for listing checkpoints
type ListCheckpointsOptions struct {
	HistoryFilter string
	IncludeAuto   bool
}

// ListCheckpoints retrieves a list of checkpoints for a sprite (excludes auto checkpoints)
func (c *Client) ListCheckpoints(ctx context.Context, spriteName string, historyFilter string) ([]*Checkpoint, error) {
	return c.ListCheckpointsWithOptions(ctx, spriteName, ListCheckpointsOptions{
		HistoryFilter: historyFilter,
		IncludeAuto:   false,
	})
}

// ListCheckpointsWithOptions retrieves a list of checkpoints with configurable options
func (c *Client) ListCheckpointsWithOptions(ctx context.Context, spriteName string, opts ListCheckpointsOptions) ([]*Checkpoint, error) {
	// Build URL with query parameters
	url := fmt.Sprintf("%s/v1/sprites/%s/checkpoints", c.baseURL, spriteName)
	sep := "?"
	if opts.HistoryFilter != "" {
		url += fmt.Sprintf("%shistory=%s", sep, opts.HistoryFilter)
		sep = "&"
	}
	if opts.IncludeAuto {
		url += fmt.Sprintf("%sincludeAuto=true", sep)
	}

	// Create request
	httpReq, err := http.NewRequestWithContext(ctx, "GET", url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))

	// Make request
	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("failed to make request: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	// Check content type
	contentType := resp.Header.Get("Content-Type")
	if strings.HasPrefix(contentType, "text/plain") {
		// History filter results - return as text
		body, _ := io.ReadAll(resp.Body)
		// For text results, we can't parse as checkpoints
		// This is a special case for history filter
		return nil, fmt.Errorf("text response not supported in SDK: %s", string(body))
	}

	// Parse JSON response
	var checkpoints []*Checkpoint
	if err := json.NewDecoder(resp.Body).Decode(&checkpoints); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	return checkpoints, nil
}

// ListCheckpoints retrieves a list of checkpoints for this sprite (excludes auto checkpoints)
func (s *Sprite) ListCheckpoints(ctx context.Context, historyFilter string) ([]*Checkpoint, error) {
	return s.client.ListCheckpoints(ctx, s.name, historyFilter)
}

// ListCheckpointsWithOptions retrieves a list of checkpoints with configurable options
func (s *Sprite) ListCheckpointsWithOptions(ctx context.Context, opts ListCheckpointsOptions) ([]*Checkpoint, error) {
	return s.client.ListCheckpointsWithOptions(ctx, s.name, opts)
}

// GetCheckpoint retrieves information about a specific checkpoint
func (c *Client) GetCheckpoint(ctx context.Context, spriteName string, checkpointID string) (*Checkpoint, error) {
	// Build URL
	url := fmt.Sprintf("%s/v1/sprites/%s/checkpoints/%s", c.baseURL, spriteName, checkpointID)

	// Create request
	httpReq, err := http.NewRequestWithContext(ctx, "GET", url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))

	// Make request
	resp, err := c.httpClient.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("failed to make request: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		return nil, fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	// Parse response
	var checkpoint Checkpoint
	if err := json.NewDecoder(resp.Body).Decode(&checkpoint); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	return &checkpoint, nil
}

// GetCheckpoint retrieves information about a specific checkpoint for this sprite
func (s *Sprite) GetCheckpoint(ctx context.Context, checkpointID string) (*Checkpoint, error) {
	return s.client.GetCheckpoint(ctx, s.name, checkpointID)
}

// RestoreCheckpoint restores a sprite from a checkpoint
func (c *Client) RestoreCheckpoint(ctx context.Context, spriteName string, checkpointID string) (*RestoreStream, error) {
	// Build URL
	url := fmt.Sprintf("%s/v1/sprites/%s/checkpoints/%s/restore", c.baseURL, spriteName, checkpointID)

	// Create request
	httpReq, err := http.NewRequestWithContext(ctx, "POST", url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	httpReq.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))

	// Use client with no timeout for streaming, but preserve transport for socket support
	streamClient := &http.Client{
		Transport: c.httpClient.Transport,
		Timeout:   0,
	}
	resp, err := streamClient.Do(httpReq)
	if err != nil {
		return nil, fmt.Errorf("failed to make request: %w", err)
	}

	if resp.StatusCode != http.StatusOK {
		body, _ := io.ReadAll(resp.Body)
		resp.Body.Close()
		return nil, fmt.Errorf("API returned status %d: %s", resp.StatusCode, string(body))
	}

	// Return streaming reader
	return &RestoreStream{
		reader:  resp.Body,
		scanner: bufio.NewScanner(resp.Body),
	}, nil
}

// RestoreCheckpoint restores this sprite from a checkpoint
func (s *Sprite) RestoreCheckpoint(ctx context.Context, checkpointID string) (*RestoreStream, error) {
	return s.client.RestoreCheckpoint(ctx, s.name, checkpointID)
}

// Next reads the next message from the checkpoint stream
func (cs *CheckpointStream) Next() (*StreamMessage, error) {
	if cs.done {
		return nil, io.EOF
	}

	if !cs.scanner.Scan() {
		cs.done = true
		if err := cs.scanner.Err(); err != nil {
			return nil, err
		}
		return nil, io.EOF
	}

	line := cs.scanner.Text()
	if line == "" {
		// Skip empty lines
		return cs.Next()
	}

	var msg StreamMessage
	if err := json.Unmarshal([]byte(line), &msg); err != nil {
		return nil, fmt.Errorf("failed to parse message: %w", err)
	}

	return &msg, nil
}

// Close closes the checkpoint stream
func (cs *CheckpointStream) Close() error {
	if cs.reader != nil {
		return cs.reader.Close()
	}
	return nil
}

// Next reads the next message from the restore stream
func (rs *RestoreStream) Next() (*StreamMessage, error) {
	if rs.done {
		return nil, io.EOF
	}

	if !rs.scanner.Scan() {
		rs.done = true
		if err := rs.scanner.Err(); err != nil {
			return nil, err
		}
		return nil, io.EOF
	}

	line := rs.scanner.Text()
	if line == "" {
		// Skip empty lines
		return rs.Next()
	}

	var msg StreamMessage
	if err := json.Unmarshal([]byte(line), &msg); err != nil {
		return nil, fmt.Errorf("failed to parse message: %w", err)
	}

	return &msg, nil
}

// Close closes the restore stream
func (rs *RestoreStream) Close() error {
	if rs.reader != nil {
		return rs.reader.Close()
	}
	return nil
}

// ProcessAll processes all messages in the checkpoint stream
func (cs *CheckpointStream) ProcessAll(handler func(*StreamMessage) error) error {
	defer cs.Close()

	for {
		msg, err := cs.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}

		if err := handler(msg); err != nil {
			return err
		}
	}

	return nil
}

// ProcessAll processes all messages in the restore stream
func (rs *RestoreStream) ProcessAll(handler func(*StreamMessage) error) error {
	defer rs.Close()

	for {
		msg, err := rs.Next()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err
		}

		if err := handler(msg); err != nil {
			return err
		}
	}

	return nil
}
