package container_test

import (
	"fmt"
	"log"
	"time"

	"github.com/superfly/sprite-env/packages/container"
	"github.com/sprite-env/packages/supervisor"
)

func ExampleNewProcess() {
	// Create a process configuration that extends supervisor.Config
	config := container.ProcessConfig{
		Config: supervisor.Config{
			Command:     "echo",
			Args:        []string{"hello", "world"},
			GracePeriod: 10 * time.Second,
		},
	}
	
	// Create the process
	process, err := container.NewProcess(config)
	if err != nil {
		log.Fatal(err)
	}
	defer process.Stop()
	
	// Start the process
	pid, err := process.Start()
	if err != nil {
		log.Fatal(err)
	}
	
	fmt.Printf("Started process with PID: %d\n", pid)
	
	// Wait for completion
	if err := process.Wait(); err != nil {
		log.Fatal(err)
	}
}

func ExampleNewProcess_withContainers() {
	// Enable containers system-wide first
	container.Configure(container.Config{
		Enabled:   true,
		SocketDir: "/var/run/containers",
	})
	
	// Create a process - TTY support is automatic when containers are enabled
	config := container.ProcessConfig{
		Config: supervisor.Config{
			Command: "crun",
			Args:    []string{"run", "mycontainer"},
		},
		TTYTimeout: 10 * time.Second,
	}
	
	// Create the process
	process, err := container.NewProcess(config)
	if err != nil {
		log.Fatal(err)
	}
	defer process.Stop()
	
	// The CONSOLE_SOCKET environment variable is automatically set
	// Get the socket path if needed
	ttyPath, _ := process.TTYPath()
	fmt.Printf("TTY socket path: %s\n", ttyPath)
	
	// Start the process
	pid, err := process.Start()
	if err != nil {
		log.Fatal(err)
	}
	
	fmt.Printf("Started container process with PID: %d\n", pid)
	
	// Wait for and get the TTY from the container runtime
	ptyFile, err := process.GetTTY()
	if err != nil {
		log.Fatal(err)
	}
	defer ptyFile.Close()
	
	fmt.Printf("Received PTY: %s\n", ptyFile.Name())
	
	// Use the PTY for I/O with the container...
}

func ExampleProcessBuilder() {
	// Use the fluent builder interface
	process, err := container.NewProcessBuilder("bash", "-c", "echo $TEST_VAR").
		WithEnv([]string{"TEST_VAR=Hello from builder!"}).
		WithDir("/tmp").
		WithGracePeriod(5 * time.Second).
		Build()
	
	if err != nil {
		log.Fatal(err)
	}
	defer process.Stop()
	
	// Start and wait
	if _, err := process.Start(); err != nil {
		log.Fatal(err)
	}
	
	if err := process.Wait(); err != nil {
		log.Fatal(err)
	}
}

func ExampleProcessBuilder_withContainers() {
	// Configure containers system-wide
	container.Configure(container.Config{
		Enabled:   true,
		SocketDir: "/var/run/containers",
	})
	
	// Builder automatically gets TTY support when containers are enabled
	process, err := container.NewProcessBuilder("crun", "run", "mycontainer").
		WithTTYTimeout(15 * time.Second).
		Build()
	
	if err != nil {
		log.Fatal(err)
	}
	defer process.Stop()
	
	// Start the container
	pid, err := process.Start()
	if err != nil {
		log.Fatal(err)
	}
	
	fmt.Printf("Container started with PID: %d\n", pid)
	
	// Get the PTY when ready
	pty, err := process.GetTTY()
	if err != nil {
		log.Fatal(err)
	}
	defer pty.Close()
	
	// Interact with container via PTY...
}