package wsexec

import (
	"strings"
	"testing"
	"time"
)

func TestOSCMonitor_BrowserOpenSequence(t *testing.T) {
	var capturedURL string
	var capturedPorts []string

	handler := func(sequence string) {
		parts := strings.Split(sequence, ";")
		if len(parts) >= 3 && parts[0] == "9999" && parts[1] == "browser-open" {
			capturedURL = parts[2]
			// Parse ports if present
			if len(parts) >= 4 && parts[3] != "" {
				capturedPorts = strings.Split(parts[3], ",")
			} else {
				capturedPorts = nil
			}
		}
	}

	monitor := NewOSCMonitor(handler)

	// Test browser open sequence with ST terminator and ports
	testURL := "https://example.com"
	testPorts := "3000,8080"
	sequence := "\033]9999;browser-open;" + testURL + ";" + testPorts + "\033\\"

	n, err := monitor.Write([]byte(sequence))
	if err != nil {
		t.Fatalf("Write failed: %v", err)
	}

	if n != len(sequence) {
		t.Errorf("Expected to write %d bytes, got %d", len(sequence), n)
	}

	// Give the async handler time to fire
	time.Sleep(10 * time.Millisecond)

	if capturedURL != testURL {
		t.Errorf("Expected URL %s, got %s", testURL, capturedURL)
	}

	expectedPorts := []string{"3000", "8080"}
	if len(capturedPorts) != len(expectedPorts) {
		t.Errorf("Expected %d ports, got %d", len(expectedPorts), len(capturedPorts))
	} else {
		for i, expected := range expectedPorts {
			if capturedPorts[i] != expected {
				t.Errorf("Expected port %s at index %d, got %s", expected, i, capturedPorts[i])
			}
		}
	}
}

func TestOSCMonitor_BrowserOpenSequenceBEL(t *testing.T) {
	var capturedURL string
	var capturedPorts []string

	handler := func(sequence string) {
		parts := strings.Split(sequence, ";")
		if len(parts) >= 3 && parts[0] == "9999" && parts[1] == "browser-open" {
			capturedURL = parts[2]
			// Parse ports if present
			if len(parts) >= 4 && parts[3] != "" {
				capturedPorts = strings.Split(parts[3], ",")
			} else {
				capturedPorts = nil
			}
		}
	}

	monitor := NewOSCMonitor(handler)

	// Test browser open sequence with BEL terminator (no ports for backward compatibility)
	testURL := "https://github.com"
	sequence := "\033]9999;browser-open;" + testURL + "\007"

	n, err := monitor.Write([]byte(sequence))
	if err != nil {
		t.Fatalf("Write failed: %v", err)
	}

	if n != len(sequence) {
		t.Errorf("Expected to write %d bytes, got %d", len(sequence), n)
	}

	// Give the async handler time to fire
	time.Sleep(10 * time.Millisecond)

	if capturedURL != testURL {
		t.Errorf("Expected URL %s, got %s", testURL, capturedURL)
	}

	// Should have no ports for backward compatibility
	if capturedPorts != nil {
		t.Errorf("Expected no ports for backward compatibility, got %v", capturedPorts)
	}
}

func TestOSCMonitor_NormalText(t *testing.T) {
	var sequenceCalled bool

	handler := func(sequence string) {
		sequenceCalled = true
	}

	monitor := NewOSCMonitor(handler)

	testText := "Hello World!\n"

	n, err := monitor.Write([]byte(testText))
	if err != nil {
		t.Fatalf("Write failed: %v", err)
	}

	if n != len(testText) {
		t.Errorf("Expected to write %d bytes, got %d", len(testText), n)
	}

	// Give any potential async handler time to fire
	time.Sleep(10 * time.Millisecond)

	if sequenceCalled {
		t.Error("Handler should not have been called for normal text")
	}
}

func TestOSCMonitor_MixedContent(t *testing.T) {
	var capturedURL string
	var capturedPorts []string

	handler := func(sequence string) {
		parts := strings.Split(sequence, ";")
		if len(parts) >= 3 && parts[0] == "9999" && parts[1] == "browser-open" {
			capturedURL = parts[2]
			// Parse ports if present
			if len(parts) >= 4 && parts[3] != "" {
				capturedPorts = strings.Split(parts[3], ",")
			} else {
				capturedPorts = nil
			}
		}
	}

	monitor := NewOSCMonitor(handler)

	// Mix normal text with browser open sequence (with empty ports)
	testURL := "https://github.com"
	content := "Before text\033]9999;browser-open;" + testURL + ";\033\\After text"

	n, err := monitor.Write([]byte(content))
	if err != nil {
		t.Fatalf("Write failed: %v", err)
	}

	if n != len(content) {
		t.Errorf("Expected to write %d bytes, got %d", len(content), n)
	}

	// Give the async handler time to fire
	time.Sleep(10 * time.Millisecond)

	if capturedURL != testURL {
		t.Errorf("Expected URL %s, got %s", testURL, capturedURL)
	}

	// Should have no ports (empty ports string)
	if capturedPorts != nil {
		t.Errorf("Expected no ports for empty ports string, got %v", capturedPorts)
	}
}

func TestOSCMonitor_NonBrowserOSCSequence(t *testing.T) {
	var sequenceCalled bool

	handler := func(sequence string) {
		sequenceCalled = true
	}

	monitor := NewOSCMonitor(handler)

	// Test non-browser OSC sequence (should not trigger handler)
	sequence := "\033]0;Window Title\033\\"

	n, err := monitor.Write([]byte(sequence))
	if err != nil {
		t.Fatalf("Write failed: %v", err)
	}

	if n != len(sequence) {
		t.Errorf("Expected to write %d bytes, got %d", len(sequence), n)
	}

	// Give any potential async handler time to fire
	time.Sleep(10 * time.Millisecond)

	if sequenceCalled {
		t.Error("Handler should not have been called for non-browser OSC sequence")
	}
}

func TestOSCMonitor_PartialBrowserSequence(t *testing.T) {
	var sequenceCalled bool

	handler := func(sequence string) {
		sequenceCalled = true
	}

	monitor := NewOSCMonitor(handler)

	// Test partial match (should not trigger handler)
	sequence := "\033]9999;other-command;data\033\\"

	n, err := monitor.Write([]byte(sequence))
	if err != nil {
		t.Fatalf("Write failed: %v", err)
	}

	if n != len(sequence) {
		t.Errorf("Expected to write %d bytes, got %d", len(sequence), n)
	}

	// Give any potential async handler time to fire
	time.Sleep(10 * time.Millisecond)

	if sequenceCalled {
		t.Error("Handler should not have been called for partial browser sequence")
	}
}

func TestOSCMonitor_IncompleteBrowserSequence(t *testing.T) {
	var sequenceCalled bool

	handler := func(sequence string) {
		sequenceCalled = true
	}

	monitor := NewOSCMonitor(handler)

	// Test incomplete sequence (no terminator)
	incomplete := "\033]9999;browser-open;https://example.com"

	n, err := monitor.Write([]byte(incomplete))
	if err != nil {
		t.Fatalf("Write failed: %v", err)
	}

	if n != len(incomplete) {
		t.Errorf("Expected to write %d bytes, got %d", len(incomplete), n)
	}

	// Give any potential async handler time to fire
	time.Sleep(10 * time.Millisecond)

	if sequenceCalled {
		t.Error("Handler should not have been called for incomplete sequence")
	}
}

func TestOSCMonitor_BrowserOpenWithPorts(t *testing.T) {
	var capturedURL string
	var capturedPorts []string

	handler := func(sequence string) {
		parts := strings.Split(sequence, ";")
		if len(parts) >= 3 && parts[0] == "9999" && parts[1] == "browser-open" {
			capturedURL = parts[2]
			// Parse ports if present
			if len(parts) >= 4 && parts[3] != "" {
				capturedPorts = strings.Split(parts[3], ",")
			} else {
				capturedPorts = nil
			}
		}
	}

	monitor := NewOSCMonitor(handler)

	// Test various port configurations
	testCases := []struct {
		name          string
		url           string
		ports         string
		expectedURL   string
		expectedPorts []string
	}{
		{
			name:          "Single port",
			url:           "https://oauth.example.com",
			ports:         "3000",
			expectedURL:   "https://oauth.example.com",
			expectedPorts: []string{"3000"},
		},
		{
			name:          "Multiple ports",
			url:           "https://auth.service.com",
			ports:         "3000,8080,9000",
			expectedURL:   "https://auth.service.com",
			expectedPorts: []string{"3000", "8080", "9000"},
		},
		{
			name:          "Empty ports",
			url:           "https://example.com",
			ports:         "",
			expectedURL:   "https://example.com",
			expectedPorts: nil,
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			// Reset captured values
			capturedURL = ""
			capturedPorts = nil

			sequence := "\033]9999;browser-open;" + tc.url + ";" + tc.ports + "\033\\"

			_, err := monitor.Write([]byte(sequence))
			if err != nil {
				t.Fatalf("Write failed: %v", err)
			}

			// Give the async handler time to fire
			time.Sleep(10 * time.Millisecond)

			if capturedURL != tc.expectedURL {
				t.Errorf("Expected URL %s, got %s", tc.expectedURL, capturedURL)
			}

			if len(capturedPorts) != len(tc.expectedPorts) {
				t.Errorf("Expected %d ports, got %d", len(tc.expectedPorts), len(capturedPorts))
			} else {
				for i, expected := range tc.expectedPorts {
					if capturedPorts[i] != expected {
						t.Errorf("Expected port %s at index %d, got %s", expected, i, capturedPorts[i])
					}
				}
			}
		})
	}
}
