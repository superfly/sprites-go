package controlapi

import (
	"context"
	"crypto/tls"
	"encoding/json"
	"errors"
	"fmt"
	"net/http"
	"net/url"
	"strings"
	"sync"
	"time"

	"github.com/gorilla/websocket"
	"github.com/superfly/sprites-go/ops"
)

// Client manages a single control websocket connection.
type Client struct {
	baseURL string // https://host/v1/sprites/{name}
	token   string

	mu   sync.Mutex
	conn *websocket.Conn
}

func NewClient(baseURL, token string) *Client {
	return &Client{baseURL: strings.TrimRight(baseURL, "/"), token: token}
}

// Dial establishes the control websocket if not connected.
func (c *Client) Dial(ctx context.Context) error {
	c.mu.Lock()
	defer c.mu.Unlock()
	if c.conn != nil {
		return nil
	}
	wsURL := c.buildWSURL()
	req, _ := http.NewRequestWithContext(ctx, http.MethodGet, wsURL, nil)
	if c.token != "" {
		req.Header.Set("Authorization", fmt.Sprintf("Bearer %s", c.token))
	}
	d := websocket.Dialer{HandshakeTimeout: 10 * time.Second}
	if strings.HasPrefix(wsURL, "wss://") {
		d.TLSClientConfig = &tls.Config{}
	}
	conn, resp, err := d.DialContext(ctx, wsURL, req.Header)
	if err != nil {
		if resp != nil && resp.StatusCode == http.StatusNotFound {
			return &NotFoundError{}
		}
		if resp != nil && resp.StatusCode != 0 {
			return fmt.Errorf("control dial failed: %w (HTTP %d)", err, resp.StatusCode)
		}
		return fmt.Errorf("control dial failed: %w", err)
	}
	c.conn = conn
	return nil
}

// StartExec sends a control op.start for exec and returns a session bound to this connection.
func (c *Client) StartExec(ctx context.Context, opt ops.ExecOptions) (ops.ExecSession, error) {
	if err := c.Dial(ctx); err != nil {
		return nil, err
	}
	cid := newControlID()
	env := map[string]any{
		"type": "op.start",
		"id":   cid,
		"op":   "exec",
		"args": buildArgs(opt),
	}
	payload, _ := json.Marshal(env)
	if err := c.writeText("control:" + string(payload)); err != nil {
		return nil, err
	}
	sess := newControlSession(c.conn, cid, opt.TTY)
	if !opt.HasStdin {
		_ = sess.sendStdinEOF()
	}
	return sess, nil
}

func (c *Client) buildWSURL() string {
	base := c.baseURL
	if strings.HasPrefix(base, "http") {
		base = "ws" + base[4:]
	}
	u, _ := url.Parse(strings.TrimRight(base, "/"))
	if !strings.HasSuffix(u.Path, "/control") {
		u.Path = strings.TrimRight(u.Path, "/") + "/control"
	}
	return u.String()
}

func (c *Client) writeText(s string) error {
	c.mu.Lock()
	defer c.mu.Unlock()
	if c.conn == nil {
		return errors.New("not connected")
	}
	return c.conn.WriteMessage(websocket.TextMessage, []byte(s))
}

func buildArgs(opt ops.ExecOptions) map[string]any {
	m := map[string]any{}
	if len(opt.Cmd) > 0 {
		m["cmd"] = opt.Cmd
		m["path"] = opt.Cmd[0]
	}
	if opt.Env != nil {
		arr := []string{}
		for k, v := range opt.Env {
			arr = append(arr, fmt.Sprintf("%s=%s", k, v))
		}
		if len(arr) > 0 {
			m["env"] = arr
		}
	}
	if opt.Workdir != "" {
		m["dir"] = opt.Workdir
	}
	if opt.TTY {
		m["tty"] = "true"
		if opt.Rows > 0 {
			m["rows"] = fmt.Sprintf("%d", opt.Rows)
		}
		if opt.Cols > 0 {
			m["cols"] = fmt.Sprintf("%d", opt.Cols)
		}
	}
	if !opt.HasStdin {
		m["stdin"] = "false"
	}
	return m
}

type NotFoundError struct{}

func (e *NotFoundError) Error() string { return "control endpoint not found" }
