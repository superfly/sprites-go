package phx

import (
	"time"
)

const (
	// defaultConnectTimeout is the default handshake timeout
	defaultConnectTimeout = 10 * time.Second

	// defaultPushTimeout is the default timeout when waiting for a reply from a pushed message
	defaultPushTimeout = 10 * time.Second

	// defaultHeartbeatInterval is the default time between heartbeats
	defaultHeartbeatInterval = 30 * time.Second

	// busyWait is the time for goroutines to sleep while waiting. Lower = more CPU. Higher = less responsive
	busyWait = 100 * time.Millisecond

	// messageQueueLength is the number of messages to queue when not connected before blocking
	messageQueueLength = 1000
)

func defaultReconnectAfterFunc(tries int) time.Duration {
	schedule := []time.Duration{10, 50, 100, 150, 200, 250, 500, 1000, 2000}
	if tries >= 1 && tries-1 < len(schedule) {
		return schedule[tries-1] * time.Millisecond
	} else {
		return 5000 * time.Millisecond
	}
}

func defaultRejoinAfterFunc(tries int) time.Duration {
	schedule := []time.Duration{1000, 2000, 5000}
	if tries >= 1 && tries-1 < len(schedule) {
		return schedule[tries-1] * time.Millisecond
	} else {
		return 10000 * time.Millisecond
	}
}

type ConnectionState int

const (
	ConnectionConnecting ConnectionState = iota
	ConnectionOpen
	ConnectionClosing
	ConnectionClosed
)

func (s ConnectionState) String() string {
	switch s {
	case ConnectionConnecting:
		return "connecting"
	case ConnectionOpen:
		return "open"
	case ConnectionClosing:
		return "closing"
	case ConnectionClosed:
		return "closed"
	}
	return "unknown"
}

type ChannelState int

const (
	ChannelClosed ChannelState = iota
	ChannelErrored
	ChannelJoined
	ChannelJoining
	ChannelLeaving
	ChannelRemoved
)

func (c ChannelState) String() string {
	switch c {
	case ChannelClosed:
		return "closed"
	case ChannelErrored:
		return "errored"
	case ChannelJoined:
		return "joined"
	case ChannelJoining:
		return "joining"
	case ChannelLeaving:
		return "leaving"
	}
	return "unknown"
}
