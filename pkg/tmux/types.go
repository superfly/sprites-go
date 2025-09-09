package tmux

import "time"

// TmuxWindow represents a tmux window
type TmuxWindow struct {
	ID        string
	Name      string
	SessionID string
	Index     int
	Layout    string
	Active    bool
	Panes     []*TmuxPane
}

// TmuxPane represents a tmux pane
type TmuxPane struct {
	ID         string
	WindowID   string
	Index      int
	Active     bool
	ByteCount  int64
	DataRate   float64 // bytes per second
	dataPoints []dataPoint
}

type dataPoint struct {
	timestamp time.Time
	bytes     int64
}

// Event types
type TmuxEvent interface{}

type SessionChangedEvent struct {
	SessionID string
	Name      string
}

type SessionsChangedEvent struct{}

type WindowAddEvent struct {
	WindowID string
}

type WindowCloseEvent struct {
	WindowID string
}

type PaneAddEvent struct {
	PaneID   string
	WindowID string
}

type PaneCloseEvent struct {
	PaneID string
}

type PaneOutputEvent struct {
	PaneID string
	Data   string
}

type LayoutChangeEvent struct {
	WindowID string
	Layout   string
}

type WindowLinkEvent struct {
	SessionID string
	WindowID  string
}

type WindowUnlinkEvent struct {
	SessionID string
	WindowID  string
}

type ClientSessionChangedEvent struct {
	ClientName string
	SessionID  string
}

type WindowRenamedEvent struct {
	WindowID string
	Name     string
}

type UnlinkedWindowCloseEvent struct {
	WindowID string
}
