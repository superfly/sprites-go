// Package endpointapi (UNSTABLE) provides low-level access to the legacy /exec endpoint.
// This package is intended for advanced users and is subject to change.
package endpointapi

import (
	"context"
	"crypto/tls"
	"fmt"
	"net/http"
	"net/url"
	"strings"
	"time"

	"github.com/gorilla/websocket"
	"github.com/superfly/sprites-go/ops"
)

type EndpointAPI struct {
	BaseURL string
	Token   string
}

// StartExec dials the legacy /exec websocket endpoint and returns a session.
func (e *EndpointAPI) StartExec(ctx context.Context, opt ops.ExecOptions) (ops.ExecSession, error) {
	wsURL, err := buildExecURL(e.BaseURL, opt)
	if err != nil {
		return nil, err
	}

	req, err := http.NewRequestWithContext(ctx, http.MethodGet, wsURL, nil)
	if err != nil {
		return nil, err
	}
	if e.Token != "" {
		req.Header.Set("Authorization", fmt.Sprintf("Bearer %s", e.Token))
	}

	d := websocket.Dialer{HandshakeTimeout: 10 * time.Second}
	if strings.HasPrefix(wsURL, "wss://") {
		d.TLSClientConfig = &tls.Config{}
	}
	conn, resp, err := d.DialContext(ctx, wsURL, req.Header)
	if err != nil {
		if resp != nil && resp.StatusCode != 0 {
			return nil, fmt.Errorf("endpoint dial failed: %w (HTTP %d)", err, resp.StatusCode)
		}
		return nil, fmt.Errorf("endpoint dial failed: %w", err)
	}

	s := newWSSession(conn, false)
	if !opt.HasStdin {
		_ = s.sendStdinEOF()
	}
	return s, nil
}

func buildExecURL(base string, opt ops.ExecOptions) (string, error) {
	if base == "" {
		return "", fmt.Errorf("base URL required")
	}
	if strings.HasPrefix(base, "http") {
		base = "ws" + base[4:]
	}
	u, err := url.Parse(strings.TrimRight(base, "/"))
	if err != nil {
		return "", fmt.Errorf("invalid base URL: %w", err)
	}
	if !strings.HasSuffix(u.Path, "/exec") {
		u.Path = strings.TrimRight(u.Path, "/") + "/exec"
	}

	q := u.Query()
	for i, c := range opt.Cmd {
		q.Add("cmd", c)
		if i == 0 {
			q.Set("path", c)
		}
	}
	for k, v := range opt.Env {
		q.Add("env", fmt.Sprintf("%s=%s", k, v))
	}
	if opt.Workdir != "" {
		q.Set("dir", opt.Workdir)
	}
	if opt.TTY {
		q.Set("tty", "true")
		if opt.Rows > 0 {
			q.Set("rows", fmt.Sprintf("%d", opt.Rows))
		}
		if opt.Cols > 0 {
			q.Set("cols", fmt.Sprintf("%d", opt.Cols))
		}
	}
	if !opt.HasStdin {
		q.Set("stdin", "false")
	}
	u.RawQuery = q.Encode()
	return u.String(), nil
}
