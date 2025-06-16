package adapters

import (
	"context"
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
