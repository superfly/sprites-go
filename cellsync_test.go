package sprites

import (
	"testing"
)

func TestEncodeDecodeFrame(t *testing.T) {
	tests := []struct {
		name      string
		frameType byte
		epoch     uint32
		flags     byte
		payload   []byte
	}{
		{
			name:      "empty payload",
			frameType: FrameAck,
			epoch:     42,
			flags:     0,
			payload:   nil,
		},
		{
			name:      "with payload",
			frameType: FrameDiff,
			epoch:     100,
			flags:     FlagCursorVisible | FlagHasRegions,
			payload:   []byte{1, 2, 3, 4, 5},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			encoded := EncodeFrame(tt.frameType, tt.epoch, tt.flags, tt.payload)
			decoded, err := DecodeFrame(encoded)
			if err != nil {
				t.Fatalf("DecodeFrame failed: %v", err)
			}

			if decoded.Type != tt.frameType {
				t.Errorf("Type mismatch: got %v, want %v", decoded.Type, tt.frameType)
			}
			if decoded.Epoch != tt.epoch {
				t.Errorf("Epoch mismatch: got %v, want %v", decoded.Epoch, tt.epoch)
			}
			if decoded.Flags != tt.flags {
				t.Errorf("Flags mismatch: got %v, want %v", decoded.Flags, tt.flags)
			}
			if string(decoded.Payload) != string(tt.payload) {
				t.Errorf("Payload mismatch: got %v, want %v", decoded.Payload, tt.payload)
			}
		})
	}
}

func TestEncodeDecodeAck(t *testing.T) {
	epochs := []uint32{0, 1, 100, 65535, 1000000}

	for _, epoch := range epochs {
		encoded := EncodeAck(epoch)
		decoded, err := DecodeFrame(encoded)
		if err != nil {
			t.Fatalf("DecodeFrame failed for epoch %d: %v", epoch, err)
		}

		if decoded.Type != FrameAck {
			t.Errorf("Type mismatch: got %v, want %v", decoded.Type, FrameAck)
		}
		if decoded.Epoch != epoch {
			t.Errorf("Epoch mismatch: got %v, want %v", decoded.Epoch, epoch)
		}
	}
}

func TestEncodeDecodeInput(t *testing.T) {
	tests := []struct {
		name  string
		event KeyEvent
	}{
		{
			name: "single key",
			event: KeyEvent{
				Type:      InputKey,
				Key:       []byte{'a'},
				Modifiers: 0,
				Seq:       1,
			},
		},
		{
			name: "key with modifiers",
			event: KeyEvent{
				Type:      InputKey,
				Key:       []byte{'c'},
				Modifiers: ModCtrl,
				Seq:       42,
			},
		},
		{
			name: "special key",
			event: KeyEvent{
				Type:      InputKey,
				Key:       []byte{KeyArrowUp},
				Modifiers: ModAlt | ModShift,
				Seq:       100,
			},
		},
		{
			name: "utf8 key",
			event: KeyEvent{
				Type:      InputKey,
				Key:       []byte("中"),
				Modifiers: 0,
				Seq:       200,
			},
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			encoded := EncodeInput(tt.event)
			decoded, err := DecodeFrame(encoded)
			if err != nil {
				t.Fatalf("DecodeFrame failed: %v", err)
			}

			if decoded.Type != FrameInput {
				t.Errorf("Type mismatch: got %v, want %v", decoded.Type, FrameInput)
			}
			if decoded.Epoch != tt.event.Seq {
				t.Errorf("Epoch/Seq mismatch: got %v, want %v", decoded.Epoch, tt.event.Seq)
			}
		})
	}
}

func TestApplyDiff(t *testing.T) {
	t.Run("initial sync creates screen", func(t *testing.T) {
		diff := &ScreenDiff{
			Resize:        true,
			Rows:          24,
			Cols:          80,
			ToEpoch:       1,
			CursorChanged: true,
			CursorRow:     0,
			CursorCol:     0,
			CursorVisible: true,
			Regions: []DiffRegion{
				{
					StartRow: 0,
					StartCol: 0,
					EndRow:   1,
					EndCol:   5,
					Cells: []Cell{
						{Char: 'H', Width: 1},
						{Char: 'e', Width: 1},
						{Char: 'l', Width: 1},
						{Char: 'l', Width: 1},
						{Char: 'o', Width: 1},
					},
				},
			},
		}

		screen := ApplyDiff(nil, diff)
		if screen == nil {
			t.Fatal("ApplyDiff returned nil for initial sync")
		}

		if screen.Rows != 24 || screen.Cols != 80 {
			t.Errorf("Size mismatch: got %dx%d, want 24x80", screen.Rows, screen.Cols)
		}
		if screen.Epoch != 1 {
			t.Errorf("Epoch mismatch: got %v, want 1", screen.Epoch)
		}

		// Check the cells were applied
		expected := "Hello"
		for i, ch := range expected {
			if screen.Cells[0][i].Char != ch {
				t.Errorf("Cell[0][%d] mismatch: got %c, want %c", i, screen.Cells[0][i].Char, ch)
			}
		}
	})

	t.Run("incremental diff updates screen", func(t *testing.T) {
		// Create initial screen
		initial := &ScreenSnapshot{
			Rows:          24,
			Cols:          80,
			Cells:         make([][]Cell, 24),
			CursorRow:     0,
			CursorCol:     0,
			CursorVisible: true,
			Epoch:         1,
		}
		for i := range initial.Cells {
			initial.Cells[i] = make([]Cell, 80)
		}
		initial.Cells[0][0] = Cell{Char: 'A', Width: 1}

		// Apply diff that changes cell
		diff := &ScreenDiff{
			FromEpoch: 1,
			ToEpoch:   2,
			Regions: []DiffRegion{
				{
					StartRow: 0,
					StartCol: 0,
					EndRow:   1,
					EndCol:   1,
					Cells:    []Cell{{Char: 'B', Width: 1}},
				},
			},
		}

		screen := ApplyDiff(initial, diff)
		if screen == nil {
			t.Fatal("ApplyDiff returned nil")
		}

		if screen.Cells[0][0].Char != 'B' {
			t.Errorf("Cell[0][0] not updated: got %c, want B", screen.Cells[0][0].Char)
		}
		if screen.Epoch != 2 {
			t.Errorf("Epoch not updated: got %v, want 2", screen.Epoch)
		}
	})

	t.Run("epoch mismatch returns nil", func(t *testing.T) {
		initial := &ScreenSnapshot{
			Rows:  24,
			Cols:  80,
			Cells: make([][]Cell, 24),
			Epoch: 5,
		}
		for i := range initial.Cells {
			initial.Cells[i] = make([]Cell, 80)
		}

		diff := &ScreenDiff{
			FromEpoch: 3, // Wrong epoch
			ToEpoch:   4,
		}

		screen := ApplyDiff(initial, diff)
		if screen != nil {
			t.Error("ApplyDiff should return nil for epoch mismatch")
		}
	})
}

func TestCellSyncSession(t *testing.T) {
	session := NewCellSyncSession()

	// Verify initial state
	if session.GetScreen() != nil {
		t.Error("Initial screen should be nil")
	}
	if session.GetLastEpoch() != 0 {
		t.Error("Initial epoch should be 0")
	}

	// Test MakeKeyEvent
	event1 := session.MakeKeyEvent([]byte{'a'}, 0)
	if event1.Seq != 1 {
		t.Errorf("First event seq should be 1, got %d", event1.Seq)
	}

	event2 := session.MakeKeyEvent([]byte{'b'}, ModCtrl)
	if event2.Seq != 2 {
		t.Errorf("Second event seq should be 2, got %d", event2.Seq)
	}
	if event2.Modifiers != ModCtrl {
		t.Errorf("Modifiers not set correctly")
	}

	// Test MakePasteEvent
	paste := session.MakePasteEvent([]byte("pasted text"))
	if paste.Type != InputPaste {
		t.Error("Paste event should have InputPaste type")
	}
	if paste.Seq != 3 {
		t.Errorf("Paste event seq should be 3, got %d", paste.Seq)
	}
}
