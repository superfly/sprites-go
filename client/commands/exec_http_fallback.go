package commands

import (
	"bytes"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"strings"
)

// runExecHTTPFallback executes the command using POST /exec and multiplexed octet-stream.
// It returns the remote exit code.
func runExecHTTPFallback(baseURL, token, spriteName string, args []string, env []string, dir string, stdin io.Reader, stdout, stderr io.Writer) (int, error) {
	if len(args) == 0 {
		return 1, fmt.Errorf("no command provided")
	}

	// Build URL: {base}/v1/sprites/{name}/exec with query params
	u, err := url.Parse(strings.TrimRight(baseURL, "/"))
	if err != nil {
		return 1, err
	}
	u.Path = "/v1/sprites/" + spriteName + "/exec"

	q := u.Query()
	for i, a := range args {
		q.Add("cmd", a)
		if i == 0 {
			q.Set("path", a)
		}
	}
	for _, e := range env {
		q.Add("env", e)
	}
	if dir != "" {
		q.Set("dir", dir)
	}
	// Enable stdin only if provided
	if stdin != nil {
		q.Set("stdin", "true")
	}
	u.RawQuery = q.Encode()

	// Prepare request body from stdin if present
	var body io.Reader
	if stdin != nil {
		// Stream directly
		body = stdin
	} else {
		body = bytes.NewReader(nil)
	}

	req, err := http.NewRequest("POST", u.String(), body)
	if err != nil {
		return 1, err
	}
	req.Header.Set("Authorization", "Bearer "+token)
	req.Header.Set("Content-Type", "application/octet-stream")

	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		return 1, err
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		b, _ := io.ReadAll(resp.Body)
		return 1, fmt.Errorf("http exec failed: status %d: %s", resp.StatusCode, string(b))
	}

	// Demux frames: 1-byte stream id + payload (no length prefix) streamed by server
	// We read in chunks and process each frame (they may be coalesced). Frames are small; process byte-wise.
	// Our server sends frames as contiguous (id + payload) with no length; treat each write as a full payload.
	// To be robust, buffer and split multiple frames.
	buf := make([]byte, 32*1024)
	exitCode := -1
	for {
		n, rerr := resp.Body.Read(buf)
		if n > 0 {
			data := buf[:n]
			// Process possibly multiple frames in data: each frame starts with id, remaining bytes belong to that frame until next id? Our server writes one frame per Write; we will split by leading id bytes.
			// Minimal parsing: iterate; when seeing id 0x01/0x02/0x03, treat the rest of this chunk as its payload.
			for len(data) > 0 {
				id := data[0]
				payload := data[1:]
				switch id {
				case 0x01: // stdout
					if len(payload) > 0 {
						_, _ = stdout.Write(payload)
					}
				case 0x02: // stderr
					if len(payload) > 0 {
						_, _ = stderr.Write(payload)
					}
				case 0x03: // exit
					if len(payload) > 0 {
						exitCode = int(payload[0])
					} else {
						exitCode = 255
					}
				default:
					// Unknown frame; write to stderr
					if len(payload) > 0 {
						_, _ = stderr.Write(payload)
					}
				}
				// This simplistic parser assumes one frame per chunk; break to read next
				break
			}
		}
		if rerr != nil {
			if rerr == io.EOF {
				break
			}
			return 1, rerr
		}
	}
	if exitCode < 0 {
		// If server closed without exit frame, treat as error
		return 1, fmt.Errorf("no exit frame received")
	}
	return exitCode, nil
}
