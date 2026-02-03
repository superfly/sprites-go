// Package sprites provides a Go SDK for interacting with Sprite environments.
// This file implements client-side cell-sync protocol support for mosh-like
// terminal synchronization.
package sprites

import (
	"encoding/binary"
	"errors"
	"unicode/utf8"
)

// Frame types for cell-sync protocol
const (
	// Server -> Client
	FrameInit   byte = 0x10 // Full screen state + dimensions
	FrameDiff   byte = 0x11 // Incremental diff against last ACKed epoch
	FrameCursor byte = 0x12 // Cursor position update only
	FrameResize byte = 0x13 // Terminal resize notification
	FrameOps    byte = 0x14 // Op-based screen update

	// Client -> Server
	FrameAck   byte = 0x20 // Acknowledge epoch
	FrameInput byte = 0x21 // Key/mouse input event
)

// Frame header format:
// [Type:1][Epoch:4][Flags:1][Length:2][Payload:...]
const FrameHeaderSize = 8

// Frame flags
const (
	FlagCursorVisible byte = 0x01
	FlagAltScreen     byte = 0x02
	FlagHasRegions    byte = 0x04
)

// Input event types
const (
	InputKey   byte = 0x00
	InputPaste byte = 0x01
	InputMouse byte = 0x02
)

// Special key codes (0x80+ for extended keys)
const (
	KeyEnter      byte = 0x0D
	KeyTab        byte = 0x09
	KeyEscape     byte = 0x1B
	KeyBackspace  byte = 0x7F
	KeyArrowUp    byte = 0x80
	KeyArrowDown  byte = 0x81
	KeyArrowLeft  byte = 0x82
	KeyArrowRight byte = 0x83
	KeyHome       byte = 0x84
	KeyEnd        byte = 0x85
	KeyPageUp     byte = 0x86
	KeyPageDown   byte = 0x87
	KeyInsert     byte = 0x88
	KeyDelete     byte = 0x89
	KeyF1         byte = 0x90
	KeyF2         byte = 0x91
	KeyF3         byte = 0x92
	KeyF4         byte = 0x93
	KeyF5         byte = 0x94
	KeyF6         byte = 0x95
	KeyF7         byte = 0x96
	KeyF8         byte = 0x97
	KeyF9         byte = 0x98
	KeyF10        byte = 0x99
	KeyF11        byte = 0x9A
	KeyF12        byte = 0x9B
)

// Modifier flags
const (
	ModCtrl  byte = 0x01
	ModAlt   byte = 0x02
	ModShift byte = 0x04
	ModMeta  byte = 0x08
)

// CellSyncMIMEType is the MIME type for cell-sync mode negotiation.
const CellSyncMIMEType = "application/vnd.sprite.cell-sync"

// KeyEvent represents a key input from the client.
type KeyEvent struct {
	Type      byte   // InputKey, InputPaste, or InputMouse
	Key       []byte // UTF-8 char or special key code
	Modifiers byte   // Modifier bitfield
	Seq       uint32 // Sequence number for ordering
}

// Frame represents a decoded cell-sync frame.
type Frame struct {
	Type    byte
	Epoch   uint32
	Flags   byte
	Payload []byte
}

// ScreenSnapshot represents a complete snapshot of terminal screen state.
type ScreenSnapshot struct {
	Rows int // Number of rows
	Cols int // Number of columns

	// Cells contains the screen content in row-major order.
	Cells [][]Cell

	// Cursor position
	CursorRow     int
	CursorCol     int
	CursorVisible bool

	// Screen mode
	AltScreen bool

	// Epoch is a monotonically increasing version number.
	Epoch uint32
}

// Cell represents a single terminal cell.
type Cell struct {
	Char      rune   // Primary character (0 = empty/space)
	Combining []rune // Combining characters (diacritics, etc.)
	Width     int    // Display width (1 for normal, 2 for wide chars)
	Attrs     CellAttrs
	FG        CellColor
	BG        CellColor
}

// CellAttrs contains text styling attributes.
type CellAttrs struct {
	Bold      bool
	Italic    bool
	Underline int // 0=off, 1=single, 2=double, 3=curly
	Blink     bool
	Reverse   bool
	Strike    bool
}

// CellColor represents a terminal color.
type CellColor struct {
	Type  ColorType
	Index uint8 // For indexed colors (0-255)
	R     uint8 // For RGB colors
	G     uint8
	B     uint8
}

// ColorType indicates how a color value should be interpreted.
type ColorType uint8

const (
	ColorDefault ColorType = 0 // Use terminal default
	ColorIndexed ColorType = 1 // 256-color palette index
	ColorRGB     ColorType = 2 // True color RGB
)

// ScreenDiff represents the changes between two screen snapshots.
type ScreenDiff struct {
	FromEpoch uint32
	ToEpoch   uint32

	Resize bool
	Rows   int
	Cols   int

	CursorChanged bool
	CursorRow     int
	CursorCol     int
	CursorVisible bool

	Regions []DiffRegion
}

// DiffRegion represents a rectangular region of changed cells.
type DiffRegion struct {
	StartRow int
	StartCol int
	EndRow   int // Exclusive
	EndCol   int // Exclusive
	Cells    []Cell
}

// IsEmpty returns true if the diff represents no changes.
func (d *ScreenDiff) IsEmpty() bool {
	return !d.Resize && !d.CursorChanged && len(d.Regions) == 0
}

// DecodeFrame parses a frame from bytes.
func DecodeFrame(data []byte) (*Frame, error) {
	if len(data) < FrameHeaderSize {
		return nil, errors.New("frame too short")
	}

	frame := &Frame{
		Type:  data[0],
		Epoch: binary.BigEndian.Uint32(data[1:5]),
		Flags: data[5],
	}

	length := binary.BigEndian.Uint16(data[6:8])
	if len(data) < FrameHeaderSize+int(length) {
		return nil, errors.New("frame payload truncated")
	}

	frame.Payload = data[FrameHeaderSize : FrameHeaderSize+int(length)]
	return frame, nil
}

// DecodeDiff decodes a DIFF or INIT frame payload into a ScreenDiff.
func DecodeDiff(frame *Frame) (*ScreenDiff, error) {
	if frame == nil || (frame.Type != FrameDiff && frame.Type != FrameInit) {
		return nil, errors.New("not a diff or init frame")
	}

	data := frame.Payload
	if len(data) < 14 { // Minimum header size
		return nil, errors.New("payload too short")
	}

	diff := &ScreenDiff{
		ToEpoch:       frame.Epoch,
		CursorVisible: (frame.Flags & FlagCursorVisible) != 0,
	}

	offset := 0
	diff.FromEpoch = binary.BigEndian.Uint32(data[offset:])
	offset += 4
	diff.Rows = int(binary.BigEndian.Uint16(data[offset:]))
	offset += 2
	diff.Cols = int(binary.BigEndian.Uint16(data[offset:]))
	offset += 2
	diff.CursorRow = int(binary.BigEndian.Uint16(data[offset:]))
	offset += 2
	diff.CursorCol = int(binary.BigEndian.Uint16(data[offset:]))
	offset += 2

	if diff.Rows > 0 || diff.Cols > 0 {
		diff.Resize = true
		diff.CursorChanged = true
	}

	regionCount := int(binary.BigEndian.Uint16(data[offset:]))
	offset += 2

	for i := 0; i < regionCount && offset+10 <= len(data); i++ {
		region := DiffRegion{
			StartRow: int(binary.BigEndian.Uint16(data[offset:])),
			StartCol: int(binary.BigEndian.Uint16(data[offset+2:])),
			EndRow:   int(binary.BigEndian.Uint16(data[offset+4:])),
			EndCol:   int(binary.BigEndian.Uint16(data[offset+6:])),
		}
		cellCount := int(binary.BigEndian.Uint16(data[offset+8:]))
		offset += 10

		region.Cells = make([]Cell, 0, cellCount)
		for j := 0; j < cellCount && offset < len(data); j++ {
			cell, n := decodeCell(data[offset:])
			region.Cells = append(region.Cells, cell)
			offset += n
		}

		diff.Regions = append(diff.Regions, region)
	}

	return diff, nil
}

// DecodeCursor decodes a CURSOR frame payload.
func DecodeCursor(frame *Frame) (row, col int, visible bool, err error) {
	if frame == nil || frame.Type != FrameCursor {
		return 0, 0, false, errors.New("not a cursor frame")
	}
	if len(frame.Payload) < 4 {
		return 0, 0, false, errors.New("cursor payload too short")
	}

	row = int(binary.BigEndian.Uint16(frame.Payload[0:]))
	col = int(binary.BigEndian.Uint16(frame.Payload[2:]))
	visible = (frame.Flags & FlagCursorVisible) != 0
	return row, col, visible, nil
}

// DecodeResize decodes a RESIZE frame payload.
func DecodeResize(frame *Frame) (rows, cols int, err error) {
	if frame == nil || frame.Type != FrameResize {
		return 0, 0, errors.New("not a resize frame")
	}
	if len(frame.Payload) < 4 {
		return 0, 0, errors.New("resize payload too short")
	}

	rows = int(binary.BigEndian.Uint16(frame.Payload[0:]))
	cols = int(binary.BigEndian.Uint16(frame.Payload[2:]))
	return rows, cols, nil
}

func decodeCell(data []byte) (Cell, int) {
	if len(data) == 0 {
		return Cell{}, 0
	}

	cell := Cell{}
	offset := 0

	// Character
	if data[0] == 0 {
		offset++
	} else {
		r, n := utf8.DecodeRune(data[offset:])
		if r == utf8.RuneError {
			offset++
		} else {
			cell.Char = r
			offset += n
		}
	}

	// Combining characters
	if offset < len(data) {
		combiningCount := int(data[offset])
		offset++
		for i := 0; i < combiningCount && offset < len(data); i++ {
			r, n := utf8.DecodeRune(data[offset:])
			if r != utf8.RuneError {
				cell.Combining = append(cell.Combining, r)
				offset += n
			} else {
				offset++
			}
		}
	}

	// Foreground color
	if offset < len(data) {
		fg, n := decodeColor(data[offset:])
		cell.FG = fg
		offset += n
	}

	// Background color
	if offset < len(data) {
		bg, n := decodeColor(data[offset:])
		cell.BG = bg
		offset += n
	}

	// Attributes
	if offset < len(data) {
		attrs := data[offset]
		cell.Attrs.Bold = (attrs & 0x01) != 0
		cell.Attrs.Italic = (attrs & 0x02) != 0
		cell.Attrs.Underline = int((attrs >> 2) & 3)
		cell.Attrs.Blink = (attrs & 0x10) != 0
		cell.Attrs.Reverse = (attrs & 0x20) != 0
		cell.Attrs.Strike = (attrs & 0x40) != 0
		offset++
	}

	// Width
	if offset < len(data) {
		cell.Width = int(data[offset])
		offset++
	}

	return cell, offset
}

func decodeColor(data []byte) (CellColor, int) {
	if len(data) == 0 {
		return CellColor{}, 0
	}

	switch data[0] {
	case 0x00:
		return CellColor{Type: ColorDefault}, 1
	case 0x01:
		if len(data) < 2 {
			return CellColor{Type: ColorDefault}, 1
		}
		return CellColor{Type: ColorIndexed, Index: data[1]}, 2
	case 0x02:
		if len(data) < 4 {
			return CellColor{Type: ColorDefault}, 1
		}
		return CellColor{Type: ColorRGB, R: data[1], G: data[2], B: data[3]}, 4
	default:
		return CellColor{Type: ColorDefault}, 1
	}
}

// EncodeFrame creates a frame with header and payload.
func EncodeFrame(frameType byte, epoch uint32, flags byte, payload []byte) []byte {
	length := len(payload)
	if length > 65535 {
		length = 65535
		payload = payload[:length]
	}

	frame := make([]byte, FrameHeaderSize+length)
	frame[0] = frameType
	binary.BigEndian.PutUint32(frame[1:5], epoch)
	frame[5] = flags
	binary.BigEndian.PutUint16(frame[6:8], uint16(length))
	copy(frame[FrameHeaderSize:], payload)

	return frame
}

// EncodeAck creates an ACK frame for the given epoch.
func EncodeAck(epoch uint32) []byte {
	return EncodeFrame(FrameAck, epoch, 0, nil)
}

// EncodeInput creates an INPUT frame for a key event.
func EncodeInput(event KeyEvent) []byte {
	// Format: [Seq:4][Type:1][Modifiers:1][KeyLen:1][Key:1-4]
	payloadLen := 4 + 1 + 1 + 1 + len(event.Key)
	payload := make([]byte, payloadLen)

	binary.BigEndian.PutUint32(payload[0:], event.Seq)
	payload[4] = event.Type
	payload[5] = event.Modifiers
	payload[6] = byte(len(event.Key))
	copy(payload[7:], event.Key)

	return EncodeFrame(FrameInput, event.Seq, 0, payload)
}

// ApplyDiff applies a diff to a snapshot, returning the new state.
// Returns nil if the diff cannot be applied (e.g., epoch mismatch).
func ApplyDiff(base *ScreenSnapshot, diff *ScreenDiff) *ScreenSnapshot {
	if diff == nil {
		return base
	}

	// For initial sync (no base), create from diff
	if base == nil {
		if !diff.Resize {
			return nil // Can't create screen without size
		}
		result := &ScreenSnapshot{
			Rows:  diff.Rows,
			Cols:  diff.Cols,
			Epoch: diff.ToEpoch,
			Cells: make([][]Cell, diff.Rows),
		}
		for row := 0; row < diff.Rows; row++ {
			result.Cells[row] = make([]Cell, diff.Cols)
		}

		// Apply cursor
		if diff.CursorChanged {
			result.CursorRow = diff.CursorRow
			result.CursorCol = diff.CursorCol
			result.CursorVisible = diff.CursorVisible
		}

		// Apply regions
		for _, region := range diff.Regions {
			applyRegion(result, region)
		}

		return result
	}

	// Epoch check - diff must apply to the base epoch
	if diff.FromEpoch != base.Epoch {
		return nil
	}

	// Clone base and apply changes
	result := cloneSnapshot(base)
	result.Epoch = diff.ToEpoch

	// Apply resize
	if diff.Resize && (diff.Rows != result.Rows || diff.Cols != result.Cols) {
		result = resizeSnapshot(result, diff.Rows, diff.Cols)
	}

	// Apply cursor change
	if diff.CursorChanged {
		result.CursorRow = diff.CursorRow
		result.CursorCol = diff.CursorCol
		result.CursorVisible = diff.CursorVisible
	}

	// Apply cell changes
	for _, region := range diff.Regions {
		applyRegion(result, region)
	}

	return result
}

func cloneSnapshot(s *ScreenSnapshot) *ScreenSnapshot {
	if s == nil {
		return nil
	}

	clone := &ScreenSnapshot{
		Rows:          s.Rows,
		Cols:          s.Cols,
		Cells:         make([][]Cell, s.Rows),
		CursorRow:     s.CursorRow,
		CursorCol:     s.CursorCol,
		CursorVisible: s.CursorVisible,
		AltScreen:     s.AltScreen,
		Epoch:         s.Epoch,
	}

	for row := 0; row < s.Rows; row++ {
		clone.Cells[row] = make([]Cell, s.Cols)
		copy(clone.Cells[row], s.Cells[row])
	}

	return clone
}

func applyRegion(s *ScreenSnapshot, region DiffRegion) {
	idx := 0
	for row := region.StartRow; row < region.EndRow && row < s.Rows; row++ {
		for col := region.StartCol; col < region.EndCol && col < s.Cols; col++ {
			if idx < len(region.Cells) {
				s.Cells[row][col] = region.Cells[idx]
			}
			idx++
		}
	}
}

func resizeSnapshot(s *ScreenSnapshot, newRows, newCols int) *ScreenSnapshot {
	result := &ScreenSnapshot{
		Rows:          newRows,
		Cols:          newCols,
		Cells:         make([][]Cell, newRows),
		CursorRow:     s.CursorRow,
		CursorCol:     s.CursorCol,
		CursorVisible: s.CursorVisible,
		AltScreen:     s.AltScreen,
		Epoch:         s.Epoch,
	}

	// Clamp cursor to new bounds
	if result.CursorRow >= newRows {
		result.CursorRow = newRows - 1
	}
	if result.CursorCol >= newCols {
		result.CursorCol = newCols - 1
	}

	// Copy existing cells
	for row := 0; row < newRows; row++ {
		result.Cells[row] = make([]Cell, newCols)
		if row < len(s.Cells) {
			copyLen := len(s.Cells[row])
			if copyLen > newCols {
				copyLen = newCols
			}
			copy(result.Cells[row], s.Cells[row][:copyLen])
		}
	}

	return result
}

// Op types for FrameOps protocol
type OpType byte

const (
	OpResize      OpType = 0x01
	OpMoveRect    OpType = 0x02
	OpScrollUp    OpType = 0x03
	OpScrollDown  OpType = 0x04
	OpPutCells    OpType = 0x05
	OpSetCursor   OpType = 0x06
	OpSetProp     OpType = 0x07
	OpPushLine    OpType = 0x08
	OpInsertLines OpType = 0x09
	OpDeleteLines OpType = 0x0A
)

// Cell encoding markers
const (
	CellRLE     byte = 0xFF // Run of N default cells
	CellTextRun byte = 0xFE // Run of same-styled text
)

// Op represents a single screen operation
type Op struct {
	Type        OpType
	Row, Col    int
	Rows, Cols  int
	ScrollCount int
	Cells       []Cell
	Cursor      struct {
		Row, Col int
		Visible  bool
	}
	Move struct {
		SrcStartRow, SrcStartCol int
		SrcEndRow, SrcEndCol     int
		DestRow, DestCol         int
	}
	InsertDelete struct {
		Row, Count         int
		TopRow, BottomRow int
	}
	Prop, Val int
}

// ScreenUpdate represents a set of operations to apply to the screen
type ScreenUpdate struct {
	Epoch uint32
	Ops   []Op
}

// DecodeScreenUpdate decodes a FrameOps payload
func DecodeScreenUpdate(frame *Frame) (*ScreenUpdate, error) {
	if frame == nil || frame.Type != FrameOps {
		return nil, errors.New("not an ops frame")
	}

	data := frame.Payload
	if len(data) < 2 {
		return nil, errors.New("payload too short")
	}

	update := &ScreenUpdate{Epoch: frame.Epoch}
	offset := 0

	numOps := int(binary.BigEndian.Uint16(data[offset:]))
	offset += 2

	for i := 0; i < numOps && offset < len(data); i++ {
		op, n := decodeOp(data[offset:])
		update.Ops = append(update.Ops, op)
		offset += n
	}

	return update, nil
}

func decodeOp(data []byte) (Op, int) {
	if len(data) < 1 {
		return Op{}, 0
	}

	op := Op{Type: OpType(data[0])}
	offset := 1

	switch op.Type {
	case OpResize:
		if len(data) < offset+4 {
			return op, offset
		}
		op.Rows = int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2
		op.Cols = int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2

	case OpMoveRect:
		if len(data) < offset+12 {
			return op, offset
		}
		op.Move.SrcStartRow = int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2
		op.Move.SrcStartCol = int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2
		op.Move.SrcEndRow = int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2
		op.Move.SrcEndCol = int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2
		op.Move.DestRow = int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2
		op.Move.DestCol = int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2

	case OpScrollUp, OpScrollDown:
		if len(data) < offset+2 {
			return op, offset
		}
		op.ScrollCount = int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2

	case OpPutCells:
		if len(data) < offset+6 {
			return op, offset
		}
		op.Row = int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2
		op.Col = int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2
		numCells := int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2
		cells, n := decodeCellsOptimized(data[offset:], numCells)
		op.Cells = cells
		offset += n

	case OpSetCursor:
		if len(data) < offset+5 {
			return op, offset
		}
		op.Cursor.Row = int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2
		op.Cursor.Col = int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2
		op.Cursor.Visible = data[offset] != 0
		offset++

	case OpSetProp:
		if len(data) < offset+5 {
			return op, offset
		}
		op.Prop = int(data[offset])
		offset++
		op.Val = int(binary.BigEndian.Uint32(data[offset:]))
		offset += 4

	case OpPushLine:
		if len(data) < offset+2 {
			return op, offset
		}
		numCells := int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2
		cells, n := decodeCellsOptimized(data[offset:], numCells)
		op.Cells = cells
		offset += n

	case OpInsertLines, OpDeleteLines:
		if len(data) < offset+8 {
			return op, offset
		}
		op.InsertDelete.Row = int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2
		op.InsertDelete.Count = int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2
		op.InsertDelete.TopRow = int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2
		op.InsertDelete.BottomRow = int(binary.BigEndian.Uint16(data[offset:]))
		offset += 2
	}

	return op, offset
}

// decodeCellsOptimized decodes cells with RLE and text run compression
func decodeCellsOptimized(data []byte, numCells int) ([]Cell, int) {
	cells := make([]Cell, 0, numCells)
	offset := 0

	for len(cells) < numCells && offset < len(data) {
		if data[offset] == CellRLE {
			// RLE run of default cells
			if offset+1 >= len(data) {
				break
			}
			count := int(data[offset+1])
			offset += 2
			for j := 0; j < count && len(cells) < numCells; j++ {
				cells = append(cells, Cell{Width: 1})
			}
		} else if data[offset] == CellTextRun {
			// Text run
			offset++
			if offset >= len(data) {
				break
			}

			// Read attributes
			attrs := decodeAttrs(data[offset])
			offset++

			// Read foreground color
			if offset >= len(data) {
				break
			}
			fg, n := decodeColor(data[offset:])
			offset += n

			// Read background color
			if offset >= len(data) {
				break
			}
			bg, n := decodeColor(data[offset:])
			offset += n

			// Read length
			if offset >= len(data) {
				break
			}
			count := int(data[offset])
			offset++

			// Read UTF-8 characters
			for j := 0; j < count && len(cells) < numCells && offset < len(data); j++ {
				var char rune
				if data[offset] == 0 {
					offset++
				} else {
					r, n := utf8.DecodeRune(data[offset:])
					if r == utf8.RuneError {
						offset++
					} else {
						char = r
						offset += n
					}
				}
				cells = append(cells, Cell{
					Char:  char,
					Width: 1,
					Attrs: attrs,
					FG:    fg,
					BG:    bg,
				})
			}
		} else {
			// Normal cell encoding
			cell, n := decodeCell(data[offset:])
			cells = append(cells, cell)
			offset += n
		}
	}
	return cells, offset
}

func decodeAttrs(b byte) CellAttrs {
	return CellAttrs{
		Bold:      (b & 0x01) != 0,
		Italic:    (b & 0x02) != 0,
		Underline: int((b >> 2) & 3),
		Blink:     (b & 0x10) != 0,
		Reverse:   (b & 0x20) != 0,
		Strike:    (b & 0x40) != 0,
	}
}

// ApplyOps applies a ScreenUpdate to a snapshot
func ApplyOps(base *ScreenSnapshot, update *ScreenUpdate) *ScreenSnapshot {
	if update == nil || len(update.Ops) == 0 {
		return base
	}

	// Create or clone screen
	var screen *ScreenSnapshot
	if base == nil {
		// Need a resize op to create screen
		for _, op := range update.Ops {
			if op.Type == OpResize {
				screen = &ScreenSnapshot{
					Rows:  op.Rows,
					Cols:  op.Cols,
					Cells: make([][]Cell, op.Rows),
				}
				for i := range screen.Cells {
					screen.Cells[i] = make([]Cell, op.Cols)
				}
				break
			}
		}
		if screen == nil {
			return nil
		}
	} else {
		screen = cloneSnapshot(base)
	}

	// Apply each op
	for _, op := range update.Ops {
		switch op.Type {
		case OpResize:
			screen = resizeSnapshot(screen, op.Rows, op.Cols)

		case OpScrollUp:
			// Scroll content up by N rows
			for i := 0; i < screen.Rows-op.ScrollCount; i++ {
				copy(screen.Cells[i], screen.Cells[i+op.ScrollCount])
			}
			// Clear bottom rows
			for i := screen.Rows - op.ScrollCount; i < screen.Rows; i++ {
				for j := range screen.Cells[i] {
					screen.Cells[i][j] = Cell{Width: 1}
				}
			}

		case OpScrollDown:
			// Scroll content down by N rows
			for i := screen.Rows - 1; i >= op.ScrollCount; i-- {
				copy(screen.Cells[i], screen.Cells[i-op.ScrollCount])
			}
			// Clear top rows
			for i := 0; i < op.ScrollCount; i++ {
				for j := range screen.Cells[i] {
					screen.Cells[i][j] = Cell{Width: 1}
				}
			}

		case OpPutCells:
			row := op.Row
			col := op.Col
			if row >= 0 && row < screen.Rows {
				for i, cell := range op.Cells {
					c := col + i
					if c >= 0 && c < screen.Cols {
						screen.Cells[row][c] = cell
					}
				}
			}

		case OpSetCursor:
			screen.CursorRow = op.Cursor.Row
			screen.CursorCol = op.Cursor.Col
			screen.CursorVisible = op.Cursor.Visible

		case OpMoveRect:
			// Copy region from src to dest
			srcRows := op.Move.SrcEndRow - op.Move.SrcStartRow
			srcCols := op.Move.SrcEndCol - op.Move.SrcStartCol
			// Make a temp copy of source region
			temp := make([][]Cell, srcRows)
			for i := 0; i < srcRows; i++ {
				temp[i] = make([]Cell, srcCols)
				srcRow := op.Move.SrcStartRow + i
				if srcRow >= 0 && srcRow < screen.Rows {
					for j := 0; j < srcCols; j++ {
						srcCol := op.Move.SrcStartCol + j
						if srcCol >= 0 && srcCol < screen.Cols {
							temp[i][j] = screen.Cells[srcRow][srcCol]
						}
					}
				}
			}
			// Copy to dest
			for i := 0; i < srcRows; i++ {
				destRow := op.Move.DestRow + i
				if destRow >= 0 && destRow < screen.Rows {
					for j := 0; j < srcCols; j++ {
						destCol := op.Move.DestCol + j
						if destCol >= 0 && destCol < screen.Cols {
							screen.Cells[destRow][destCol] = temp[i][j]
						}
					}
				}
			}

		case OpInsertLines:
			// Insert blank lines at position, scrolling content down
			row := op.InsertDelete.Row
			count := op.InsertDelete.Count
			bottom := op.InsertDelete.BottomRow
			if bottom == 0 {
				bottom = screen.Rows
			}
			// Shift lines down
			for i := bottom - 1; i >= row+count; i-- {
				copy(screen.Cells[i], screen.Cells[i-count])
			}
			// Clear inserted lines
			for i := row; i < row+count && i < bottom; i++ {
				for j := range screen.Cells[i] {
					screen.Cells[i][j] = Cell{Width: 1}
				}
			}

		case OpDeleteLines:
			// Delete lines at position, scrolling content up
			row := op.InsertDelete.Row
			count := op.InsertDelete.Count
			bottom := op.InsertDelete.BottomRow
			if bottom == 0 {
				bottom = screen.Rows
			}
			// Shift lines up
			for i := row; i < bottom-count; i++ {
				copy(screen.Cells[i], screen.Cells[i+count])
			}
			// Clear bottom lines
			for i := bottom - count; i < bottom; i++ {
				for j := range screen.Cells[i] {
					screen.Cells[i][j] = Cell{Width: 1}
				}
			}

		case OpPushLine:
			// Legacy: PUSH_LINE is no longer sent by server.
			// Client should capture scrollback from its own buffer on OpScrollUp.
			// Kept for backwards compatibility with older servers.
		}
	}

	screen.Epoch = update.Epoch
	return screen
}

// CellSyncSession provides a high-level interface for cell-sync mode.
type CellSyncSession struct {
	screen    *ScreenSnapshot
	lastEpoch uint32
	inputSeq  uint32
}

// NewCellSyncSession creates a new cell-sync session.
func NewCellSyncSession() *CellSyncSession {
	return &CellSyncSession{}
}

// HandleFrame processes a received frame and returns true if the screen was updated.
func (s *CellSyncSession) HandleFrame(frame *Frame) (updated bool, err error) {
	switch frame.Type {
	case FrameInit, FrameDiff:
		diff, err := DecodeDiff(frame)
		if err != nil {
			return false, err
		}
		newScreen := ApplyDiff(s.screen, diff)
		if newScreen != nil {
			s.screen = newScreen
			s.lastEpoch = diff.ToEpoch
			return true, nil
		}
		return false, nil

	case FrameOps:
		update, err := DecodeScreenUpdate(frame)
		if err != nil {
			return false, err
		}
		newScreen := ApplyOps(s.screen, update)
		if newScreen != nil {
			s.screen = newScreen
			s.lastEpoch = update.Epoch
			return true, nil
		}
		return false, nil

	case FrameCursor:
		row, col, visible, err := DecodeCursor(frame)
		if err != nil {
			return false, err
		}
		if s.screen != nil {
			s.screen.CursorRow = row
			s.screen.CursorCol = col
			s.screen.CursorVisible = visible
			return true, nil
		}
		return false, nil

	case FrameResize:
		rows, cols, err := DecodeResize(frame)
		if err != nil {
			return false, err
		}
		if s.screen != nil {
			s.screen = resizeSnapshot(s.screen, rows, cols)
			return true, nil
		}
		return false, nil

	default:
		return false, nil
	}
}

// GetScreen returns the current screen state.
func (s *CellSyncSession) GetScreen() *ScreenSnapshot {
	return s.screen
}

// GetLastEpoch returns the last received epoch.
func (s *CellSyncSession) GetLastEpoch() uint32 {
	return s.lastEpoch
}

// MakeKeyEvent creates a KeyEvent for a single key press.
func (s *CellSyncSession) MakeKeyEvent(key []byte, modifiers byte) KeyEvent {
	s.inputSeq++
	return KeyEvent{
		Type:      InputKey,
		Key:       key,
		Modifiers: modifiers,
		Seq:       s.inputSeq,
	}
}

// MakePasteEvent creates a KeyEvent for pasting text.
func (s *CellSyncSession) MakePasteEvent(text []byte) KeyEvent {
	s.inputSeq++
	return KeyEvent{
		Type: InputPaste,
		Key:  text,
		Seq:  s.inputSeq,
	}
}
