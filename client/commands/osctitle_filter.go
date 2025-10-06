package commands

import (
	"io"
)

// osctitleFilterWriter removes OSC 0 title sequences from the stream.
// It forwards all other bytes to the underlying writer.
// When an OSC 0 sequence is detected, it triggers setTerminalTitle with a fixed title.
type osctitleFilterWriter struct {
	w           io.Writer
	title       string
	state       int
	buf         []byte
}

// States for simple OSC parser
const (
	stNormal = iota
	stEsc
	stOsc
	stOscString
)

func newOSCTitleFilterWriter(w io.Writer, title string) *osctitleFilterWriter {
	return &osctitleFilterWriter{w: w, title: title}
}

func (f *osctitleFilterWriter) Write(p []byte) (int, error) {
	// Process byte-by-byte to detect OSC 0 sequences and swallow them
	for _, b := range p {
		switch f.state {
		case stNormal:
			if b == 0x1b { // ESC
				f.state = stEsc
				f.buf = f.buf[:0]
				f.buf = append(f.buf, b)
				continue
			}
			if _, err := f.w.Write([]byte{b}); err != nil {
				return 0, err
			}
		case stEsc:
			f.buf = append(f.buf, b)
			if b == ']' { // OSC
				f.state = stOsc
				continue
			}
			// Not OSC, flush buffer
			if _, err := f.w.Write(f.buf); err != nil {
				return 0, err
			}
			f.state = stNormal
		case stOsc:
			f.buf = append(f.buf, b)
			// Expecting: "0;"
			if len(f.buf) >= 4 { // ESC ] 0 ;
				if f.buf[0] == 0x1b && f.buf[1] == ']' && f.buf[2] == '0' && f.buf[3] == ';' {
					f.state = stOscString
					continue
				}
				// Not OSC 0; — flush buffer and return to normal
				if _, err := f.w.Write(f.buf); err != nil {
					return 0, err
				}
				f.state = stNormal
			}
		case stOscString:
			// Accumulate until BEL (0x07) or ST (ESC \)
			f.buf = append(f.buf, b)
			if b == 0x07 { // BEL terminator
				setTerminalTitle(f.title)
				f.state = stNormal
				continue
			}
			// Check for ST
			if len(f.buf) >= 2 && f.buf[len(f.buf)-2] == 0x1b && f.buf[len(f.buf)-1] == '\\' {
				setTerminalTitle(f.title)
				f.state = stNormal
				continue
			}
			// Keep buffering
		}
	}
	return len(p), nil
}
