package supervisor_test

import (
	"fmt"
	"log"
	"syscall"
	"time"

	"github.com/sprite-env/server/packages/supervisor"
)

func ExampleSupervisor() {
	// Create a supervisor for a simple echo command
	s, err := supervisor.New(supervisor.Config{
		Command:     "echo",
		Args:        []string{"-n", "test"},
		GracePeriod: 5 * time.Second,
	})
	if err != nil {
		log.Fatal(err)
	}

	// Start the process
	_, err = s.Start()
	if err != nil {
		log.Fatal(err)
	}

	// Wait for the process to complete
	if err := s.Wait(); err != nil {
		log.Printf("Process exited with error: %v", err)
	}

	// Output:
	// test
}

func ExampleSupervisor_longRunning() {
	// Create a supervisor for a long-running process
	s, err := supervisor.New(supervisor.Config{
		Command:     "sleep",
		Args:        []string{"60"},
		GracePeriod: 2 * time.Second,
	})
	if err != nil {
		log.Fatal(err)
	}

	// Start the process
	pid, err := s.Start()
	if err != nil {
		log.Fatal(err)
	}

	// Show the process ID
	fmt.Printf("Started process with PID: %d\n", pid)

	// Run for a while
	time.Sleep(2 * time.Second)

	// Stop the process gracefully
	if err := s.Stop(); err != nil {
		log.Fatal(err)
	}

	fmt.Println("Process stopped successfully")
}

func ExampleSupervisor_signalForwarding() {
	// Create a supervisor for a process that handles signals
	s, err := supervisor.New(supervisor.Config{
		Command:     "sleep",
		Args:        []string{"30"},
		GracePeriod: 5 * time.Second,
	})
	if err != nil {
		log.Fatal(err)
	}

	// Start the process
	_, err = s.Start()
	if err != nil {
		log.Fatal(err)
	}

	// Send a signal to the process
	if err := s.Signal(syscall.SIGUSR1); err != nil {
		log.Printf("Failed to send signal: %v", err)
	}

	// Stop the process
	if err := s.Stop(); err != nil {
		log.Fatal(err)
	}
}
