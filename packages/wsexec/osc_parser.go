package wsexec

import (
	"bytes"
)

// OSCHandler is a function that handles OSC sequences
type OSCHandler func(sequence string)

// OSCMonitor monitors data for our specific OSC sequence without modifying anything
type OSCMonitor struct {
	handler OSCHandler
	buffer  bytes.Buffer
	state   parseState
}

type parseState int

const (
	stateNormal parseState = iota
	stateEscape
	stateCheckOSC
	stateBrowserSequence
)

// NewOSCMonitor creates a new OSC monitor that just scans for browser sequences
func NewOSCMonitor(handler OSCHandler) *OSCMonitor {
	return &OSCMonitor{
		handler: handler,
		state:   stateNormal,
	}
}

// Our target sequence prefix
const browserSequencePrefix = "9999;browser-open;"

// Write implements io.Writer - monitors the data but doesn't actually write anything
func (m *OSCMonitor) Write(data []byte) (int, error) {
	m.Monitor(data)
	return len(data), nil
}

// Monitor scans the data for our browser-open sequence
func (m *OSCMonitor) Monitor(data []byte) {
	for _, b := range data {
		switch m.state {
		case stateNormal:
			if b == 0x1B { // ESC
				m.state = stateEscape
				m.buffer.Reset()
				m.buffer.WriteByte(b)
			}

		case stateEscape:
			m.buffer.WriteByte(b)
			if b == ']' { // OSC introducer
				m.state = stateCheckOSC
			} else {
				// Not an OSC sequence, reset
				m.state = stateNormal
			}

		case stateCheckOSC:
			m.buffer.WriteByte(b)

			// Check if we're building our target sequence
			currentData := m.buffer.Bytes()[2:] // Skip ESC ]

			if len(currentData) <= len(browserSequencePrefix) {
				// Still checking prefix
				if len(currentData) == len(browserSequencePrefix) {
					if string(currentData) == browserSequencePrefix {
						// Found our sequence! Switch to browser parsing mode
						m.state = stateBrowserSequence
					} else {
						// Not our sequence, reset
						m.state = stateNormal
					}
				} else {
					// Check if current data is still a prefix of our target
					if !bytes.HasPrefix([]byte(browserSequencePrefix), currentData) {
						// Not our sequence, reset
						m.state = stateNormal
					}
				}
			} else {
				// Sequence too long, not ours
				m.state = stateNormal
			}

		case stateBrowserSequence:
			m.buffer.WriteByte(b)

			// Look for terminators
			if b == 0x07 { // BEL terminator
				m.handleBrowserSequence()
				m.state = stateNormal
			} else if len(m.buffer.Bytes()) >= 2 {
				bufBytes := m.buffer.Bytes()
				bufLen := len(bufBytes)
				// Check for ESC \ terminator
				if bufBytes[bufLen-2] == 0x1B && bufBytes[bufLen-1] == '\\' {
					m.handleBrowserSequence()
					m.state = stateNormal
				}
			}

			// Prevent unbounded buffer growth
			if m.buffer.Len() > 1024 {
				m.state = stateNormal
				m.buffer.Reset()
			}
		}
	}
}

// handleBrowserSequence extracts and handles our browser sequence
func (m *OSCMonitor) handleBrowserSequence() {
	bufBytes := m.buffer.Bytes()

	// Remove ESC ] prefix and terminator
	start := 2 // Skip ESC ]
	end := len(bufBytes)

	// Remove terminator
	if end >= 2 && bufBytes[end-2] == 0x1B && bufBytes[end-1] == '\\' {
		end -= 2 // Remove ESC \
	} else if end >= 1 && bufBytes[end-1] == 0x07 {
		end -= 1 // Remove BEL
	}

	if end > start {
		sequence := string(bufBytes[start:end])
		if m.handler != nil {
			// Fire the event asynchronously so it doesn't block anything
			go m.handler(sequence)
		}
	}

	m.buffer.Reset()
}
