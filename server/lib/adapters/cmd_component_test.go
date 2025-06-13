package adapters

import (
	"context"
	"testing"
	"time"
)

func TestComponentBasicLifecycle(t *testing.T) {
	config := CmdComponentConfig{
		StartCommand: []string{"echo", "hello"},
		// No ready command - should emit ready immediately
	}

	component := NewCmdComponent(config)
	ctx := context.Background()

	events := component.Events()
	err := component.Start(ctx)
	if err != nil {
		t.Fatalf("Failed to start component: %v", err)
	}

	var receivedEvents []ComponentEventType
	for event := range events {
		receivedEvents = append(receivedEvents, event)
		if event == ComponentStopped || event == ComponentFailed {
			break
		}
	}

	// Should see: Starting -> Started -> Ready -> Stopped
	expectedEvents := []ComponentEventType{
		ComponentStarting,
		ComponentStarted,
		ComponentReady,
		ComponentStopped,
	}

	if len(receivedEvents) != len(expectedEvents) {
		t.Fatalf("Expected %d events, got %d: %v", len(expectedEvents), len(receivedEvents), receivedEvents)
	}

	for i, expected := range expectedEvents {
		if receivedEvents[i] != expected {
			t.Errorf("Event %d: expected %v, got %v", i, expected, receivedEvents[i])
		}
	}
}

func TestComponentWithReadyScript(t *testing.T) {
	config := CmdComponentConfig{
		StartCommand: []string{"sh", "-c", "echo 'started'; sleep 1; echo 'output'"},
		ReadyCommand: []string{"grep", "output"},
	}

	component := NewCmdComponent(config)
	ctx := context.Background()

	events := component.Events()
	err := component.Start(ctx)
	if err != nil {
		t.Fatalf("Failed to start component: %v", err)
	}

	var receivedEvents []ComponentEventType
	timeout := time.After(5 * time.Second)

	for {
		select {
		case event, ok := <-events:
			if !ok {
				// Channel closed
				goto done
			}
			receivedEvents = append(receivedEvents, event)
			if event == ComponentStopped || event == ComponentFailed {
				goto done
			}
		case <-timeout:
			t.Fatal("Test timed out")
		}
	}

done:
	// Should see: Starting -> Started -> Checking -> Ready -> Stopped
	expectedSequence := []ComponentEventType{
		ComponentStarting,
		ComponentStarted,
		ComponentChecking,
		ComponentReady,
		ComponentStopped,
	}

	if len(receivedEvents) < len(expectedSequence) {
		t.Fatalf("Expected at least %d events, got %d: %v", len(expectedSequence), len(receivedEvents), receivedEvents)
	}

	for i, expected := range expectedSequence {
		if i >= len(receivedEvents) || receivedEvents[i] != expected {
			t.Errorf("Event %d: expected %v, got %v", i, expected, receivedEvents[i])
		}
	}
}
