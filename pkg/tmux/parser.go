package tmux

import (
	"strconv"
	"strings"
	"time"
)

// ParseLine processes a single line of tmux control mode output
func (p *TmuxControlModeParser) ParseLine(line string) {
	// Skip empty lines
	if line == "" {
		return
	}

	// Handle different message types
	switch {
	case strings.HasPrefix(line, "%begin"):
		parts := strings.Fields(line)
		if len(parts) >= 2 {
			p.pendingCommand = parts[1]
		}
	case strings.HasPrefix(line, "%end"):
		p.pendingCommand = ""
	case strings.HasPrefix(line, "%error"):
		p.pendingCommand = ""
	case strings.HasPrefix(line, "%"):
		// Control messages
		p.handleControlMessage(line)
	default:
		// Output within a command block
		if p.pendingCommand != "" {
			// This is command output, not a control message
		}
	}
}

func (p *TmuxControlModeParser) handleControlMessage(line string) {
	// Remove % prefix
	line = strings.TrimPrefix(line, "%")

	// Parse the control message type
	parts := strings.SplitN(line, " ", 2)
	if len(parts) == 0 {
		return
	}

	msgType := parts[0]
	var args string
	if len(parts) > 1 {
		args = parts[1]
	}

	switch msgType {
	case "session-changed":
		p.handleSessionChanged(args)
	case "sessions-changed":
		p.handleSessionsChanged()
	case "window-add":
		p.handleWindowAdd(args)
	case "window-close":
		p.handleWindowClose(args)
	case "pane-add", "pane-set-active":
		p.handlePaneAdd(args)
	case "pane-died", "pane-exited":
		p.handlePaneClose(args)
	case "output":
		p.handleOutput(args)
	case "layout-change":
		p.handleLayoutChange(args)
	case "window-linked":
		p.handleWindowLinked(args)
	case "window-unlinked":
		p.handleWindowUnlinked(args)
	case "client-session-changed":
		p.handleClientSessionChanged(args)
	case "window-renamed":
		p.handleWindowRenamed(args)
	case "unlinked-window-close":
		p.handleUnlinkedWindowClose(args)
	}
}

func (p *TmuxControlModeParser) handleSessionChanged(args string) {
	parts := strings.Fields(args)
	if len(parts) >= 2 {
		sessionID := parts[0]
		name := strings.Join(parts[1:], " ")
		select {
		case p.events <- SessionChangedEvent{SessionID: sessionID, Name: name}:
		default:
		}
	}
}

func (p *TmuxControlModeParser) handleSessionsChanged() {
	select {
	case p.events <- SessionsChangedEvent{}:
	default:
	}
}

func (p *TmuxControlModeParser) handleWindowAdd(args string) {
	windowID := strings.TrimSpace(args)
	if windowID == "" {
		return
	}

	// Create window
	window := &TmuxWindow{
		ID:    windowID,
		Panes: make([]*TmuxPane, 0),
	}
	p.windows[windowID] = window

	// Check if we have any unmapped panes for this window
	for paneID, pane := range p.unmappedPanes {
		if pane.WindowID == windowID {
			window.Panes = append(window.Panes, pane)
			delete(p.unmappedPanes, paneID)
			p.panes[paneID] = pane
		}
	}

	select {
	case p.events <- WindowAddEvent{WindowID: windowID}:
	default:
	}
}

func (p *TmuxControlModeParser) handleWindowClose(args string) {
	windowID := strings.TrimSpace(args)
	if windowID == "" {
		return
	}

	if window, ok := p.windows[windowID]; ok {
		// Move all panes to unmapped
		for _, pane := range window.Panes {
			p.unmappedPanes[pane.ID] = pane
			delete(p.panes, pane.ID)
		}
		delete(p.windows, windowID)
	}

	select {
	case p.events <- WindowCloseEvent{WindowID: windowID}:
	default:
	}
}

func (p *TmuxControlModeParser) handlePaneAdd(args string) {
	parts := strings.Fields(args)
	if len(parts) >= 2 {
		paneID := parts[0]
		windowID := parts[1]

		pane := &TmuxPane{
			ID:         paneID,
			WindowID:   windowID,
			dataPoints: make([]dataPoint, 0, 100),
		}

		// Try to add to window
		if window, ok := p.windows[windowID]; ok {
			window.Panes = append(window.Panes, pane)
			p.panes[paneID] = pane
		} else {
			// Window doesn't exist yet, store as unmapped
			p.unmappedPanes[paneID] = pane
		}

		select {
		case p.events <- PaneAddEvent{PaneID: paneID, WindowID: windowID}:
		default:
		}
	}
}

func (p *TmuxControlModeParser) handlePaneClose(args string) {
	paneID := strings.TrimSpace(args)
	if paneID == "" {
		return
	}

	// Remove from window if mapped
	if pane, ok := p.panes[paneID]; ok {
		if window, ok := p.windows[pane.WindowID]; ok {
			for i, wp := range window.Panes {
				if wp.ID == paneID {
					window.Panes = append(window.Panes[:i], window.Panes[i+1:]...)
					break
				}
			}
		}
		delete(p.panes, paneID)
	}

	// Also check unmapped
	delete(p.unmappedPanes, paneID)

	select {
	case p.events <- PaneCloseEvent{PaneID: paneID}:
	default:
	}
}

func (p *TmuxControlModeParser) handleOutput(args string) {
	parts := strings.SplitN(args, " ", 2)
	if len(parts) < 2 {
		return
	}

	paneID := parts[0]
	data := parseOctalString(parts[1])

	// Update byte count and data rate
	now := time.Now()
	byteCount := int64(len(data))

	if pane, ok := p.panes[paneID]; ok {
		pane.ByteCount += byteCount

		// Add data point
		pane.dataPoints = append(pane.dataPoints, dataPoint{
			timestamp: now,
			bytes:     byteCount,
		})

		// Calculate data rate
		p.updatePaneDataRate(pane, now)

		// Update window data rate
		if window, ok := p.windows[pane.WindowID]; ok {
			p.updateWindowDataRate(window)
		}
	} else if pane, ok := p.unmappedPanes[paneID]; ok {
		pane.ByteCount += byteCount

		// Add data point
		pane.dataPoints = append(pane.dataPoints, dataPoint{
			timestamp: now,
			bytes:     byteCount,
		})

		// Calculate data rate
		p.updatePaneDataRate(pane, now)
	}

	select {
	case p.events <- PaneOutputEvent{PaneID: paneID, Data: data}:
	default:
	}
}

func (p *TmuxControlModeParser) updatePaneDataRate(pane *TmuxPane, now time.Time) {
	// Remove old data points
	cutoff := now.Add(-p.dataRateWindow)
	i := 0
	for i < len(pane.dataPoints) && pane.dataPoints[i].timestamp.Before(cutoff) {
		i++
	}
	if i > 0 {
		pane.dataPoints = pane.dataPoints[i:]
	}

	// Calculate rate
	if len(pane.dataPoints) > 0 {
		firstTime := pane.dataPoints[0].timestamp
		duration := now.Sub(firstTime).Seconds()
		if duration > 0 {
			totalBytes := int64(0)
			for _, dp := range pane.dataPoints {
				totalBytes += dp.bytes
			}
			pane.DataRate = float64(totalBytes) / duration
		}
	}
}

func (p *TmuxControlModeParser) updateWindowDataRate(window *TmuxWindow) {
	// Window data rate is sum of pane rates
	totalRate := 0.0
	for _, pane := range window.Panes {
		totalRate += pane.DataRate
	}
	// Note: we don't store window data rate in the struct currently
}

func (p *TmuxControlModeParser) handleLayoutChange(args string) {
	parts := strings.SplitN(args, " ", 2)
	if len(parts) >= 2 {
		windowID := parts[0]
		layout := parts[1]

		if window, ok := p.windows[windowID]; ok {
			window.Layout = layout
		}

		select {
		case p.events <- LayoutChangeEvent{WindowID: windowID, Layout: layout}:
		default:
		}
	}
}

func (p *TmuxControlModeParser) handleWindowLinked(args string) {
	parts := strings.Fields(args)
	if len(parts) >= 2 {
		sessionID := parts[0]
		windowID := parts[1]

		select {
		case p.events <- WindowLinkEvent{SessionID: sessionID, WindowID: windowID}:
		default:
		}
	}
}

func (p *TmuxControlModeParser) handleWindowUnlinked(args string) {
	parts := strings.Fields(args)
	if len(parts) >= 2 {
		sessionID := parts[0]
		windowID := parts[1]

		select {
		case p.events <- WindowUnlinkEvent{SessionID: sessionID, WindowID: windowID}:
		default:
		}
	}
}

func (p *TmuxControlModeParser) handleClientSessionChanged(args string) {
	parts := strings.Fields(args)
	if len(parts) >= 2 {
		clientName := parts[0]
		sessionID := parts[1]

		select {
		case p.events <- ClientSessionChangedEvent{ClientName: clientName, SessionID: sessionID}:
		default:
		}
	}
}

func (p *TmuxControlModeParser) handleWindowRenamed(args string) {
	parts := strings.SplitN(args, " ", 2)
	if len(parts) >= 2 {
		windowID := parts[0]
		name := parts[1]

		if window, ok := p.windows[windowID]; ok {
			window.Name = name
		}

		select {
		case p.events <- WindowRenamedEvent{WindowID: windowID, Name: name}:
		default:
		}
	}
}

func (p *TmuxControlModeParser) handleUnlinkedWindowClose(args string) {
	windowID := strings.TrimSpace(args)
	if windowID == "" {
		return
	}

	select {
	case p.events <- UnlinkedWindowCloseEvent{WindowID: windowID}:
	default:
	}
}

// parseOctalString converts tmux's octal-encoded output to a regular string
func parseOctalString(s string) string {
	var result strings.Builder
	i := 0

	for i < len(s) {
		if i+3 < len(s) && s[i] == '\\' && s[i+1] >= '0' && s[i+1] <= '7' {
			// Try to parse octal sequence
			octalStr := s[i+1 : i+4]
			if val, err := strconv.ParseInt(octalStr, 8, 32); err == nil {
				result.WriteByte(byte(val))
				i += 4
				continue
			}
		}
		// Regular character
		result.WriteByte(s[i])
		i++
	}

	return result.String()
}
