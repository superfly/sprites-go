package controlapi

import (
	"context"

	"github.com/superfly/sprites-go/ops"
)

type API struct {
	pool *Pool
}

func NewAPI(pool *Pool) *API { return &API{pool: pool} }

func (a *API) StartExec(ctx context.Context, opt ops.ExecOptions) (ops.ExecSession, error) {
	c, err := a.pool.Checkout(ctx)
	if err != nil {
		return nil, err
	}
	sess, err := c.StartExec(ctx, opt)
	// Return connection to pool on completion happens when caller closes sess.
	// We wrap Close to checkin.
	if err != nil {
		a.pool.Checkin(c)
		return nil, err
	}
	return &pooledSession{ExecSession: sess, pool: a.pool, client: c}, nil
}

type pooledSession struct {
	ops.ExecSession
	pool   *Pool
	client *Client
}

func (p *pooledSession) Close() error {
	_ = p.ExecSession.Close()
	p.pool.Checkin(p.client)
	return nil
}
