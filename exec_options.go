package sprites

import (
	"context"
	"fmt"
)

// SetDetachable enables detachable mode for the command, creating a tmux session
func (c *Cmd) SetDetachable(detachable bool) {
	c.mu.Lock()
	defer c.mu.Unlock()

	if c.started {
		panic("sprite: SetDetachable after process started")
	}

	// Detachable sessions require TTY
	if detachable {
		c.tty = true
	}

	c.detachable = detachable
}

// SetControlMode enables tmux control mode (requires detachable or session ID)
func (c *Cmd) SetControlMode(enable bool) error {
	c.mu.Lock()
	defer c.mu.Unlock()

	if c.started {
		return fmt.Errorf("sprite: SetControlMode after process started")
	}

	if enable && !c.detachable && c.sessionID == "" {
		return fmt.Errorf("sprite: control mode requires detachable or session ID")
	}

	c.controlMode = enable
	return nil
}

// CreateDetachableSession creates a new detachable tmux session
func (c *Client) CreateDetachableSession(spriteName string, cmd string, args ...string) *Cmd {
	return c.CreateDetachableSessionWithOrg(spriteName, cmd, nil, args...)
}

// CreateDetachableSessionWithOrg creates a new detachable tmux session with organization information
func (c *Client) CreateDetachableSessionWithOrg(spriteName string, cmd string, org *OrganizationInfo, args ...string) *Cmd {
	sprite := &Sprite{
		name:   spriteName,
		client: c,
		org:    org,
	}

	command := sprite.Command(cmd, args...)
	command.SetDetachable(true)

	return command
}

// CreateDetachableSession creates a new detachable tmux session on this sprite
func (s *Sprite) CreateDetachableSession(cmd string, args ...string) *Cmd {
	command := s.Command(cmd, args...)
	command.SetDetachable(true)

	return command
}

// CreateDetachableSessionContext creates a new detachable tmux session with context
func (c *Client) CreateDetachableSessionContext(ctx context.Context, spriteName string, cmd string, args ...string) *Cmd {
	command := c.CreateDetachableSession(spriteName, cmd, args...)
	command.ctx = ctx
	return command
}

// CreateDetachableSessionContext creates a new detachable tmux session with context on this sprite
func (s *Sprite) CreateDetachableSessionContext(ctx context.Context, cmd string, args ...string) *Cmd {
	command := s.CreateDetachableSession(cmd, args...)
	command.ctx = ctx
	return command
}

// We need to add these fields to the Cmd struct (in exec.go)
// detachable  bool
// controlMode bool

// Let's create a patch to add these fields
