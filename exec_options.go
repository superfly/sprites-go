package sprites

import (
	"fmt"
)

// SetControlMode enables control mode (requires session ID)
func (c *Cmd) SetControlMode(enable bool) error {
	c.mu.Lock()
	defer c.mu.Unlock()

	if c.started {
		return fmt.Errorf("sprite: SetControlMode after process started")
	}

	if enable && c.sessionID == "" {
		return fmt.Errorf("sprite: control mode requires session ID")
	}

	c.controlMode = enable
	return nil
}
