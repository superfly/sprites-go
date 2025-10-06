package commands

import (
	"io"
	"log/slog"
)

// osctitleFilterWriter intercepts OSC 0 title sequences from the stream.
// It forwards all other bytes to the underlying writer.
// When an OSC 0 sequence is detected, it prefixes the remote title with our local prefix.
type osctitleFilterWriter struct {
	w           io.Writer
	titlePrefix string
	state       int
	buf         []byte
	titleBuf    []byte
	logger      *slog.Logger
}

// States for simple OSC parser
const (
	stNormal = iota
	stEsc
	stOsc
	stOscString
)

func newOSCTitleFilterWriter(w io.Writer, titlePrefix string, logger *slog.Logger) *osctitleFilterWriter {
	return &osctitleFilterWriter{w: w, titlePrefix: titlePrefix, logger: logger}
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
				// Extract the remote title (everything after "ESC]0;")
				remoteTitle := string(f.buf[4 : len(f.buf)-1]) // Skip "ESC]0;" and BEL
				// Prefix with our local title
				prefixedTitle := f.titlePrefix
				if remoteTitle != "" {
					if prefixedTitle != "" {
						prefixedTitle = prefixedTitle + ": " + remoteTitle
					} else {
						prefixedTitle = remoteTitle
					}
				}
				if f.logger != nil {
					f.logger.Debug("OSC title detected (BEL)",
						"remote_title", remoteTitle,
						"prefix", f.titlePrefix,
						"final_title", prefixedTitle)
				}
				setTerminalTitle(prefixedTitle, f.logger)
				f.state = stNormal
				continue
			}
			// Check for ST
			if len(f.buf) >= 2 && f.buf[len(f.buf)-2] == 0x1b && f.buf[len(f.buf)-1] == '\\' {
				// Extract the remote title (everything after "ESC]0;" and before "ESC\")
				remoteTitle := string(f.buf[4 : len(f.buf)-2]) // Skip "ESC]0;" and "ESC\"
				// Prefix with our local title
				prefixedTitle := f.titlePrefix
				if remoteTitle != "" {
					if prefixedTitle != "" {
						prefixedTitle = prefixedTitle + ": " + remoteTitle
					} else {
						prefixedTitle = remoteTitle
					}
				}
				if f.logger != nil {
					f.logger.Debug("OSC title detected (ST)",
						"remote_title", remoteTitle,
						"prefix", f.titlePrefix,
						"final_title", prefixedTitle)
				}
				setTerminalTitle(prefixedTitle, f.logger)
				f.state = stNormal
				continue
			}
			// Keep buffering
		}
	}
	return len(p), nil
}
