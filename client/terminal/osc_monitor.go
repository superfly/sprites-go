package terminal

import (
	"bytes"
)

// OSCHandler is a function that handles OSC sequences.
type OSCHandler func(sequence string)

// OSCMonitor monitors data for our specific OSC sequence without modifying anything.
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

// NewOSCMonitor creates a new OSC monitor that scans for browser sequences.
func NewOSCMonitor(handler OSCHandler) *OSCMonitor {
	return &OSCMonitor{
		handler: handler,
		state:   stateNormal,
	}
}

// Our target sequence prefix
const browserSequencePrefix = "9999;browser-open;"

// Write implements io.Writer - monitors the data but doesn't actually write anything.
func (m *OSCMonitor) Write(data []byte) (int, error) {
	m.Monitor(data)
	return len(data), nil
}

// Monitor scans the data for our browser-open sequence.
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
				m.state = stateNormal
			}

		case stateCheckOSC:
			m.buffer.WriteByte(b)
			currentData := m.buffer.Bytes()[2:] // Skip ESC ]

			if len(currentData) <= len(browserSequencePrefix) {
				if len(currentData) == len(browserSequencePrefix) {
					if string(currentData) == browserSequencePrefix {
						m.state = stateBrowserSequence
					} else {
						m.state = stateNormal
					}
				}
			} else {
				if !bytes.HasPrefix([]byte(browserSequencePrefix), currentData) {
					m.state = stateNormal
				}
			}

		case stateBrowserSequence:
			m.buffer.WriteByte(b)

			// Look for terminators
			if b == 0x07 { // BEL terminator
				m.handleBrowserSequence()
				m.state = stateNormal
			} else if len(m.buffer.Bytes()) >= 2 {
				buf := m.buffer.Bytes()
				if buf[len(buf)-2] == 0x1B && buf[len(buf)-1] == '\\' {
					m.handleBrowserSequence()
					m.state = stateNormal
				}
			}

			if m.buffer.Len() > 1024 {
				m.state = stateNormal
				m.buffer.Reset()
			}
		}
	}
}

// handleBrowserSequence extracts and handles our browser sequence.
func (m *OSCMonitor) handleBrowserSequence() {
	buf := m.buffer.Bytes()
	start := 2 // Skip ESC ]
	end := len(buf)

	// Remove terminator
	if end >= 2 && buf[end-2] == 0x1B && buf[end-1] == '\\' {
		end -= 2
	} else if end >= 1 && buf[end-1] == 0x07 {
		end -= 1
	}

	if end > start {
		seq := string(buf[start:end])
		if m.handler != nil {
			go m.handler(seq)
		}
	}
	m.buffer.Reset()
}
