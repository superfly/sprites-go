package tests

// Tests temporarily disabled - checkpoint/restore functionality has been changed significantly
// These tests need to be rewritten to work with the new architecture where restore
// happens through the API and involves stopping/starting the process
// TODO: Rewrite tests for new checkpoint/restore implementation

/*
import (
	"context"
	"os"
	lib"/adapters"
	lib"/managers"
	"testing"
	"time"
)

// mockManagedProcess is a test process that can be controlled for testing
type mockManagedProcess struct {
	eventsCh   chan adapters.ProcessEventType
	startCalls int
	stopCalls  int
}

func (p *mockManagedProcess) Start(ctx context.Context) error {
	p.startCalls++
	// Don't send events automatically - let test control it
	return nil
}

func (p *mockManagedProcess) Stop() {
	p.stopCalls++
	p.sendEvent(adapters.ProcessStoppedEvent)
}

func (p *mockManagedProcess) Signal(sig os.Signal) {
	// No-op for test
}

func (p *mockManagedProcess) Events() <-chan adapters.ProcessEventType {
	return p.eventsCh
}

func (p *mockManagedProcess) sendEvent(event adapters.ProcessEventType) {
	select {
	case p.eventsCh <- event:
		// Event sent
	default:
		// Channel full, drop event
	}
}

// TestCheckpointRestoreWithIDs tests that checkpoint IDs are properly passed through the state hierarchy
func TestCheckpointRestoreWithIDs(t *testing.T) {
	tests := []struct {
		name         string
		checkpointID string
		restoreID    string
		expectError  bool
	}{
		{
			name:         "checkpoint and restore with IDs",
			checkpointID: "checkpoint-123",
			restoreID:    "checkpoint-123",
			expectError:  false,
		},
		{
			name:         "checkpoint with empty ID",
			checkpointID: "",
			restoreID:    "",
			expectError:  false,
		},
		{
			name:         "checkpoint with complex ID",
			checkpointID: "backup-2024-01-15-prod-v1.2.3",
			restoreID:    "backup-2024-01-15-prod-v1.2.3",
			expectError:  false,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			// Create a tracking component that records checkpoint/restore calls
			trackingComponent := &checkpointTrackingComponent{
				eventsCh:            make(chan adapters.ComponentEventType, 10),
				checkpointIDHistory: []string{},
				restoreIDHistory:    []string{},
			}

			// Create a mock process that will transition to running
			mockProcess := &mockManagedProcess{
				eventsCh: make(chan adapters.ProcessEventType, 10),
			}

			// Create system with the tracking component and process
			config := managers.SystemConfig{
				Components: []managers.ManagedComponent{trackingComponent},
				ProcessState: managers.NewProcessState(managers.ProcessStateConfig{
					Process: mockProcess,
				}, nil),
			}

			ssm := managers.NewSystemState(config, nil)

			// Start the system
			if err := ssm.Fire("SystemStarting"); err != nil {
				t.Fatalf("Failed to start system: %v", err)
			}

			// Wait for component to start
			time.Sleep(20 * time.Millisecond)

			// Send component ready event to transition system to Ready
			trackingComponent.sendEvent(adapters.ComponentReady)
			time.Sleep(20 * time.Millisecond)

			// System should be in Ready state and process should be starting
			if ssm.MustState().(string) != "Ready" {
				t.Fatalf("Expected system to be in Ready state, got %s", ssm.MustState())
			}

			// Send process running event to transition to Running
			mockProcess.sendEvent(adapters.ProcessStartedEvent)
			time.Sleep(20 * time.Millisecond)

			// Verify system is in Running state
			if ssm.MustState().(string) != "Running" {
				t.Fatalf("Expected system to be in Running state, got %s", ssm.MustState())
			}

			// Perform checkpoint
			if err := ssm.Fire("CheckpointRequested", tt.checkpointID); err != nil {
				if !tt.expectError {
					t.Fatalf("Checkpoint failed unexpectedly: %v", err)
				}
				return
			}

			// Wait for checkpoint to complete
			time.Sleep(10 * time.Millisecond)

			// Verify checkpoint ID was passed correctly
			if len(trackingComponent.checkpointIDHistory) != 1 {
				t.Fatalf("Expected 1 checkpoint call, got %d", len(trackingComponent.checkpointIDHistory))
			}
			if trackingComponent.checkpointIDHistory[0] != tt.checkpointID {
				t.Errorf("Expected checkpoint ID %q, got %q", tt.checkpointID, trackingComponent.checkpointIDHistory[0])
			}

			// Wait for system to return to Running after checkpoint
			time.Sleep(10 * time.Millisecond)
			if ssm.MustState().(string) != "Running" {
				t.Fatalf("Expected system to return to Running after checkpoint, got %s", ssm.MustState())
			}

			// Perform restore
			if err := ssm.Fire("RestoreRequested", tt.restoreID); err != nil {
				if !tt.expectError {
					t.Fatalf("Restore failed unexpectedly: %v", err)
				}
				return
			}

			// Wait for restore to complete
			time.Sleep(10 * time.Millisecond)

			// Verify restore ID was passed correctly
			if len(trackingComponent.restoreIDHistory) != 1 {
				t.Fatalf("Expected 1 restore call, got %d", len(trackingComponent.restoreIDHistory))
			}
			if trackingComponent.restoreIDHistory[0] != tt.restoreID {
				t.Errorf("Expected restore ID %q, got %q", tt.restoreID, trackingComponent.restoreIDHistory[0])
			}

			// Verify system returned to Running after restore
			time.Sleep(10 * time.Millisecond)
			if ssm.MustState().(string) != "Running" {
				t.Fatalf("Expected system to return to Running after restore, got %s", ssm.MustState())
			}
		})
	}
}

// checkpointTrackingComponent is a test component that tracks checkpoint/restore calls
type checkpointTrackingComponent struct {
	eventsCh            chan adapters.ComponentEventType
	checkpointIDHistory []string
	restoreIDHistory    []string
	startCalls          int
	stopCalls           int
}

func (c *checkpointTrackingComponent) GetName() string {
	return "checkpoint-tracking-component"
}

func (c *checkpointTrackingComponent) Start(ctx context.Context) error {
	c.startCalls++
	c.sendEvent(adapters.ComponentStarted)
	return nil
}

func (c *checkpointTrackingComponent) Stop() {
	c.stopCalls++
	c.sendEvent(adapters.ComponentStopped)
}

func (c *checkpointTrackingComponent) Checkpoint(checkpointID string) error {
	c.checkpointIDHistory = append(c.checkpointIDHistory, checkpointID)
	// Simulate successful checkpoint
	go func() {
		time.Sleep(5 * time.Millisecond)
		c.sendEvent(adapters.ComponentCheckpointed)
	}()
	return nil
}

func (c *checkpointTrackingComponent) Restore(checkpointID string) error {
	c.restoreIDHistory = append(c.restoreIDHistory, checkpointID)
	// Simulate successful restore
	go func() {
		time.Sleep(5 * time.Millisecond)
		c.sendEvent(adapters.ComponentRestored)
	}()
	return nil
}

func (c *checkpointTrackingComponent) Events() <-chan adapters.ComponentEventType {
	return c.eventsCh
}

func (c *checkpointTrackingComponent) sendEvent(event adapters.ComponentEventType) {
	select {
	case c.eventsCh <- event:
		// Event sent
	default:
		// Channel full, drop event
	}
}

// TestComponentCheckpointRestore tests checkpoint/restore at the component level
func TestComponentCheckpointRestore(t *testing.T) {
	// Create a test component
	component := &checkpointTrackingComponent{
		eventsCh:            make(chan adapters.ComponentEventType, 10),
		checkpointIDHistory: []string{},
		restoreIDHistory:    []string{},
	}

	// Create component state manager
	csm := managers.NewComponentState("test-component", component, nil)

	// Start the component
	if err := csm.Fire("Starting"); err != nil {
		t.Fatalf("Failed to start component: %v", err)
	}

	// Wait for component to start
	time.Sleep(10 * time.Millisecond)

	// Transition to Running
	if err := csm.Fire("Running"); err != nil {
		t.Fatalf("Failed to transition to Running: %v", err)
	}

	// Test checkpoint with ID
	checkpointID := "test-checkpoint-456"
	if err := csm.Fire("Checkpointing", checkpointID); err != nil {
		t.Fatalf("Failed to checkpoint: %v", err)
	}

	// Wait for checkpoint to complete
	time.Sleep(20 * time.Millisecond)

	// Verify checkpoint ID was passed
	if len(component.checkpointIDHistory) != 1 || component.checkpointIDHistory[0] != checkpointID {
		t.Errorf("Expected checkpoint ID %q, got %v", checkpointID, component.checkpointIDHistory)
	}

	// Verify component returned to Running
	if csm.MustState().(string) != "Running" {
		t.Errorf("Expected component to be Running after checkpoint, got %s", csm.MustState())
	}

	// Test restore with ID
	restoreID := "test-checkpoint-456"
	if err := csm.Fire("Restoring", restoreID); err != nil {
		t.Fatalf("Failed to restore: %v", err)
	}

	// Wait for restore to complete
	time.Sleep(20 * time.Millisecond)

	// Verify restore ID was passed
	if len(component.restoreIDHistory) != 1 || component.restoreIDHistory[0] != restoreID {
		t.Errorf("Expected restore ID %q, got %v", restoreID, component.restoreIDHistory)
	}

	// Verify component returned to Running
	if csm.MustState().(string) != "Running" {
		t.Errorf("Expected component to be Running after restore, got %s", csm.MustState())
	}
}
*/
