package lib

import (
	"os"
	"path/filepath"
	"sprite-env/lib/states"
	"testing"
	"time"
)

// dummyEnv implements the Environment interface but does nothing
// (used to satisfy ProcessManager's constructor)
type dummyEnv struct{}

func (d *dummyEnv) UpdateComponentState(component, newState, oldState string) {}
func (d *dummyEnv) UpdateProcessState(newState, oldState string)              {}

func TestProcess_ExitZero(t *testing.T) {
	scriptPath := filepath.Join("..", "test-scripts", "_shared", "exit_zero.sh")
	pm := NewProcessManager(nil, true, scriptPath)
	err := pm.Start()
	if err != nil {
		t.Fatalf("failed to start process: %v", err)
	}
	time.Sleep(100 * time.Millisecond)
	if pm.GetState() != states.ProcessStateStopped {
		t.Errorf("expected state Stopped, got %s", pm.GetState())
	}
	if pm.GetExitCode() != 0 {
		t.Errorf("expected exit code 0, got %d", pm.GetExitCode())
	}
}

func TestProcess_ExitNonZero(t *testing.T) {
	scriptPath := filepath.Join("..", "test-scripts", "_shared", "exit_nonzero.sh")
	pm := NewProcessManager(nil, true, scriptPath)
	err := pm.Start()
	if err != nil {
		t.Fatalf("failed to start process: %v", err)
	}
	time.Sleep(100 * time.Millisecond)
	if pm.GetState() != states.ProcessStateCrashed {
		t.Errorf("expected state Crashed, got %s", pm.GetState())
	}
	if pm.GetExitCode() != 42 {
		t.Errorf("expected exit code 42, got %d", pm.GetExitCode())
	}
}

func TestProcess_PrintOutput(t *testing.T) {
	scriptPath := filepath.Join("..", "test-scripts", "_shared", "print_args.sh")
	pm := NewProcessManager(nil, true, scriptPath, "hello world")
	err := pm.Start()
	if err != nil {
		t.Fatalf("failed to start process: %v", err)
	}
	time.Sleep(100 * time.Millisecond)
	if pm.GetState() != states.ProcessStateStopped {
		t.Errorf("expected state Stopped, got %s", pm.GetState())
	}
}

func TestProcess_SleepAndStop(t *testing.T) {
	scriptPath := filepath.Join("..", "test-scripts", "_shared", "run_forever.sh")
	pm := NewProcessManager(nil, true, scriptPath)
	err := pm.Start()
	if err != nil {
		t.Fatalf("failed to start process: %v", err)
	}
	time.Sleep(100 * time.Millisecond)
	if pm.GetState() != states.ProcessStateRunning {
		t.Errorf("expected state Running, got %s", pm.GetState())
	}
	err = pm.Stop()
	if err != nil {
		t.Fatalf("failed to stop process: %v", err)
	}
	if pm.GetState() != states.ProcessStateKilled {
		t.Errorf("expected state Killed, got %s", pm.GetState())
	}
}

func TestProcess_IgnoreSigterm(t *testing.T) {
	scriptPath := filepath.Join("..", "test-scripts", "_shared", "ignore_signals.sh")
	pm := NewProcessManager(nil, true, scriptPath)
	err := pm.Start()
	if err != nil {
		t.Fatalf("failed to start process: %v", err)
	}
	time.Sleep(100 * time.Millisecond)
	if pm.GetState() != states.ProcessStateRunning {
		t.Errorf("expected state Running, got %s", pm.GetState())
	}
	err = pm.Stop()
	if err != nil {
		t.Fatalf("failed to stop process: %v", err)
	}
	if pm.GetState() != states.ProcessStateKilled {
		t.Errorf("expected state Killed, got %s", pm.GetState())
	}
}

func TestProcess_MissingScript(t *testing.T) {
	pm := NewProcessManager(&dummyEnv{}, true, "/nonexistent/script.sh", "")
	err := pm.Start()
	if err == nil {
		t.Fatalf("expected error for missing script, got nil")
	}
	if pm.GetState() != states.ProcessStateError {
		t.Errorf("expected state to be Error, got %s", pm.GetState())
	}
}

func TestProcess_NonExecutableScript(t *testing.T) {
	// Create a temporary non-executable file
	tmpFile := t.TempDir() + "/non_executable.sh"
	if err := os.WriteFile(tmpFile, []byte("#!/bin/bash\necho hello"), 0644); err != nil {
		t.Fatalf("failed to create test file: %v", err)
	}

	pm := NewProcessManager(&dummyEnv{}, true, tmpFile, "")
	err := pm.Start()
	if err == nil {
		t.Fatalf("expected error for non-executable script, got nil")
	}
	if pm.GetState() != states.ProcessStateError {
		t.Errorf("expected state to be Error, got %s", pm.GetState())
	}
}

func TestProcess_InvalidCommand(t *testing.T) {
	pm := NewProcessManager(&dummyEnv{}, true, "this_command_does_not_exist", "")
	err := pm.Start()
	if err == nil {
		t.Fatalf("expected error for invalid command, got nil")
	}
	if pm.GetState() != states.ProcessStateError {
		t.Errorf("expected state to be Error, got %s", pm.GetState())
	}
}

func TestProcess_AbsolutePath(t *testing.T) {
	scriptPath := filepath.Join("..", "test-scripts", "_shared", "exit_zero.sh")
	absPath, err := filepath.Abs(scriptPath)
	if err != nil {
		t.Fatalf("failed to get absolute path: %v", err)
	}

	pm := NewProcessManager(&dummyEnv{}, true, absPath)
	err = pm.Start()
	if err != nil {
		t.Fatalf("failed to start process with absolute path: %v", err)
	}
	time.Sleep(100 * time.Millisecond)
	if err := pm.Stop(); err != nil {
		t.Errorf("failed to stop process: %v", err)
	}
}

func TestProcess_RelativePath(t *testing.T) {
	scriptPath := filepath.Join("..", "test-scripts", "_shared", "exit_zero.sh")
	pm := NewProcessManager(&dummyEnv{}, true, scriptPath)
	err := pm.Start()
	if err != nil {
		t.Fatalf("failed to start process with relative path: %v", err)
	}
	time.Sleep(100 * time.Millisecond)
	if err := pm.Stop(); err != nil {
		t.Errorf("failed to stop process: %v", err)
	}
}

func TestProcess_RelativePathWithArgs(t *testing.T) {
	scriptPath := filepath.Join("..", "test-scripts", "_shared", "print_args.sh")
	pm := NewProcessManager(&dummyEnv{}, true, scriptPath, "arg1 arg2")
	err := pm.Start()
	if err != nil {
		t.Fatalf("failed to start process with relative path and args: %v", err)
	}
	time.Sleep(100 * time.Millisecond)
	if err := pm.Stop(); err != nil {
		t.Errorf("failed to stop process: %v", err)
	}
}
