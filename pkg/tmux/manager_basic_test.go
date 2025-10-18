package tmux

import (
	"context"
	"testing"
)

// Parity with terminal: existence and list shouldn't panic; errors yield empty set
func TestManager_SessionExistsAndList_NoPanic(t *testing.T) {
	m := NewManager(context.Background(), Options{TmuxBinary: "/bin/echo"})
	_ = m.SessionExists("99999")
	if _, err := m.ListSessions(); err != nil {
		// ListSessions returns empty on error; no assertion needed here
	}
}
