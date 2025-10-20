package controlapi

import (
	"context"
	"sync"
)

// Pool maintains a small set of open control connections.
type Pool struct {
	newClient func() *Client

	mu      sync.Mutex
	idle    []*Client
	open    int
	maxOpen int
}

func NewPool(newClient func() *Client, maxOpen int) *Pool {
	return &Pool{newClient: newClient, maxOpen: maxOpen}
}

// Checkout returns an existing idle client or dials a new connection.
func (p *Pool) Checkout(ctx context.Context) (*Client, error) {
	p.mu.Lock()
	n := len(p.idle)
	if n > 0 {
		c := p.idle[n-1]
		p.idle = p.idle[:n-1]
		p.mu.Unlock()
		// ensure connected
		if err := c.Dial(ctx); err != nil {
			return nil, err
		}
		return c, nil
	}
	// create new
	p.open++
	p.mu.Unlock()

	c := p.newClient()
	if err := c.Dial(ctx); err != nil {
		p.mu.Lock()
		p.open--
		p.mu.Unlock()
		return nil, err
	}
	return c, nil
}

// Checkin returns a client to the pool or closes it if above maxOpen.
func (p *Pool) Checkin(c *Client) {
	if c == nil {
		return
	}
	p.mu.Lock()
	if p.open > p.maxOpen {
		p.open--
		p.mu.Unlock()
		_ = c.conn.Close()
		return
	}
	p.idle = append(p.idle, c)
	p.mu.Unlock()
}
