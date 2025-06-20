package adapters

import (
	"context"
	"os"
	"path/filepath"
	"testing"
	"time"
)

func TestCmdComponentBasicLifecycle(t *testing.T) {
	component := NewCmdComponent(CmdComponentConfig{
		StartCommand: []string{"sh", "-c", "echo hello; sleep 0.1"},
	})

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	err := component.Start(ctx)
	if err != nil {
		t.Fatalf("Failed to start component: %v", err)
	}

	// Listen to events from the component
	events := component.Events()
	var receivedEvents []ComponentEventType
	timeout := time.After(2 * time.Second)

eventLoop:
	for {
		select {
		case event := <-events:
			receivedEvents = append(receivedEvents, event)
			if event == ComponentStopped {
				break eventLoop
			}
		case <-timeout:
			t.Fatalf("Timeout waiting for events. Received: %v", receivedEvents)
		}
	}

	// For component with no ReadyCommand, ComponentReady should be emitted after ComponentStarted
	expectedEvents := []ComponentEventType{ComponentStarting, ComponentStarted, ComponentReady, ComponentStopped}
	if len(receivedEvents) != len(expectedEvents) {
		t.Fatalf("Expected %d events, got %d: %v", len(expectedEvents), len(receivedEvents), receivedEvents)
	}

	for i, expected := range expectedEvents {
		if receivedEvents[i] != expected {
			t.Errorf("Event %d: expected %s, got %s", i, expected, receivedEvents[i])
		}
	}
}

func TestCmdComponentWithReadyScript(t *testing.T) {
	component := NewCmdComponent(CmdComponentConfig{
		StartCommand: []string{"sh", "-c", "echo started; sleep 0.1; echo output"},
		ReadyCommand: []string{"sh", "-c", "read line && echo $line"},
	})

	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	err := component.Start(ctx)
	if err != nil {
		t.Fatalf("Failed to start component: %v", err)
	}

	// Listen to events from the component
	events := component.Events()
	var receivedEvents []ComponentEventType
	timeout := time.After(2 * time.Second)

eventLoop:
	for {
		select {
		case event := <-events:
			receivedEvents = append(receivedEvents, event)
			if event == ComponentStopped {
				break eventLoop
			}
		case <-timeout:
			t.Fatalf("Timeout waiting for events. Received: %v", receivedEvents)
		}
	}

	expectedEvents := []ComponentEventType{ComponentStarting, ComponentStarted, ComponentChecking, ComponentReady, ComponentStopped}
	if len(receivedEvents) != len(expectedEvents) {
		t.Fatalf("Expected %d events, got %d: %v", len(expectedEvents), len(receivedEvents), receivedEvents)
	}

	for i, expected := range expectedEvents {
		if receivedEvents[i] != expected {
			t.Errorf("Event %d: expected %s, got %s", i, expected, receivedEvents[i])
		}
	}
}

func TestCmdComponentReadyScriptThatDoesntRead(t *testing.T) {
	// Test component with ready script that exits immediately without reading stdin
	// This should not cause deadlocks
	component := NewCmdComponent(CmdComponentConfig{
		StartCommand: []string{"sh", "-c", "echo started; sleep 0.1; echo output"},
		ReadyCommand: []string{"sh", "-c", "echo 'ready check failed' >&2; exit 1"}, // Exits without reading stdin
		ReadyTimeout: 1 * time.Second,
	})

	ctx, cancel := context.WithTimeout(context.Background(), 3*time.Second)
	defer cancel()

	err := component.Start(ctx)
	if err != nil {
		t.Fatalf("Failed to start component: %v", err)
	}

	// Listen to events from the component
	events := component.Events()
	var receivedEvents []ComponentEventType
	timeout := time.After(2 * time.Second)

eventLoop:
	for {
		select {
		case event := <-events:
			receivedEvents = append(receivedEvents, event)
			if event == ComponentFailed || event == ComponentStopped {
				break eventLoop
			}
		case <-timeout:
			t.Fatalf("Timeout waiting for events. Received: %v", receivedEvents)
		}
	}

	// Should get starting, started, checking, then failed (not hanging forever)
	expectedEvents := []ComponentEventType{ComponentStarting, ComponentStarted, ComponentChecking, ComponentFailed}
	if len(receivedEvents) != len(expectedEvents) {
		t.Fatalf("Expected %d events, got %d: %v", len(expectedEvents), len(receivedEvents), receivedEvents)
	}

	for i, expected := range expectedEvents {
		if receivedEvents[i] != expected {
			t.Errorf("Event %d: expected %s, got %s", i, expected, receivedEvents[i])
		}
	}
}

func TestCmdComponentWithRealTestScripts(t *testing.T) {
	tests := []struct {
		name               string
		startScript        string
		readyScript        string
		expectedFinalEvent ComponentEventType
		shouldTimeout      bool
	}{
		{
			name:               "healthy component",
			startScript:        "../../test-scripts/_shared/healthy_start.sh",
			readyScript:        "../../test-scripts/_shared/healthy_ready.sh",
			expectedFinalEvent: ComponentReady,
			shouldTimeout:      false,
		},
		{
			name:               "ready fails component",
			startScript:        "../../test-scripts/_shared/healthy_start.sh",
			readyScript:        "../../test-scripts/_shared/ready_fails.sh",
			expectedFinalEvent: ComponentFailed,
			shouldTimeout:      false,
		},
		{
			name:               "ready never succeeds component",
			startScript:        "../../test-scripts/_shared/healthy_start.sh",
			readyScript:        "../../test-scripts/_shared/ready_never_succeeds.sh",
			expectedFinalEvent: ComponentFailed,
			shouldTimeout:      true,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			component := NewCmdComponent(CmdComponentConfig{
				Name:         tt.name,
				StartCommand: []string{tt.startScript},
				ReadyCommand: []string{tt.readyScript},
				ReadyTimeout: 2 * time.Second, // Short timeout for testing
			})

			ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
			defer cancel()

			err := component.Start(ctx)
			if err != nil {
				t.Fatalf("Failed to start component: %v", err)
			}

			// Listen to events from the component
			events := component.Events()
			var receivedEvents []ComponentEventType
			timeout := time.After(4 * time.Second)

		eventLoop:
			for {
				select {
				case event := <-events:
					t.Logf("Received event: %s", event)
					receivedEvents = append(receivedEvents, event)
					if event == ComponentReady || event == ComponentFailed || event == ComponentStopped {
						break eventLoop
					}
				case <-timeout:
					if tt.shouldTimeout {
						// This is expected for ready_never_succeeds.sh
						t.Logf("Expected timeout occurred for %s", tt.name)
						break eventLoop
					} else {
						t.Fatalf("Unexpected timeout waiting for events in %s. Received: %v", tt.name, receivedEvents)
					}
				}
			}

			// Verify we got the expected final event
			if len(receivedEvents) == 0 {
				if tt.shouldTimeout {
					// For timeout cases, we might not get any final event, which is OK
					return
				}
				t.Fatalf("No events received for %s", tt.name)
			}

			finalEvent := receivedEvents[len(receivedEvents)-1]
			if !tt.shouldTimeout && finalEvent != tt.expectedFinalEvent {
				t.Errorf("Expected final event %s, got %s for %s. All events: %v",
					tt.expectedFinalEvent, finalEvent, tt.name, receivedEvents)
			}

			// Verify we always get the basic startup events
			if len(receivedEvents) < 2 {
				t.Errorf("Expected at least starting and started events for %s, got: %v", tt.name, receivedEvents)
			} else {
				if receivedEvents[0] != ComponentStarting {
					t.Errorf("Expected first event to be ComponentStarting for %s, got %s", tt.name, receivedEvents[0])
				}
				if receivedEvents[1] != ComponentStarted {
					t.Errorf("Expected second event to be ComponentStarted for %s, got %s", tt.name, receivedEvents[1])
				}
			}

			// Stop the component
			component.Stop()
		})
	}
}

func TestCmdComponentEnvironmentVariables(t *testing.T) {
	// Set test environment variable
	os.Setenv("TEST_COMPONENT_VAR", "component_test_value")
	defer os.Unsetenv("TEST_COMPONENT_VAR")

	tmpDir := t.TempDir()

	// Create start script that echoes env var
	startScript := filepath.Join(tmpDir, "start.sh")
	if err := os.WriteFile(startScript, []byte(`#!/bin/bash
echo "Start script TEST_COMPONENT_VAR=$TEST_COMPONENT_VAR"
exec sleep 10
`), 0755); err != nil {
		t.Fatal(err)
	}

	// Create ready script that checks env var
	readyScript := filepath.Join(tmpDir, "ready.sh")
	if err := os.WriteFile(readyScript, []byte(`#!/bin/bash
read -t 1 line
if [ "$TEST_COMPONENT_VAR" = "component_test_value" ]; then
	echo "Ready script TEST_COMPONENT_VAR is correct"
	exit 0
else
	echo "Ready script TEST_COMPONENT_VAR is wrong: $TEST_COMPONENT_VAR"
	exit 1
fi
`), 0755); err != nil {
		t.Fatal(err)
	}

	component := NewCmdComponent(CmdComponentConfig{
		Name:         "test-env-component",
		StartCommand: []string{startScript},
		ReadyCommand: []string{readyScript},
		ReadyTimeout: 2 * time.Second,
	})
	defer component.Close()

	ctx := context.Background()

	// Start component
	err := component.Start(ctx)
	if err != nil {
		t.Fatalf("Failed to start component: %v", err)
	}

	// Wait for ready event
	events := component.Events()
	timeout := time.After(3 * time.Second)
	gotReady := false

	for !gotReady {
		select {
		case event := <-events:
			t.Logf("Received event: %v", event)
			if event == ComponentReady {
				gotReady = true
			} else if event == ComponentFailed {
				t.Fatal("Component failed instead of becoming ready")
			}
		case <-timeout:
			t.Fatal("Timeout waiting for ready event")
		}
	}

	// Stop the component
	component.Stop()
}
