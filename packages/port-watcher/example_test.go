package portwatcher_test

import (
	"fmt"
	"log"
	"net"
	"os"
	"time"

	portwatcher "github.com/superfly/sprite-env/packages/port-watcher"
)

func Example() {
	// Create a callback function that will be called when new ports are detected
	callback := func(port portwatcher.Port) {
		fmt.Printf("New port detected: %s:%d (PID: %d)\n",
			port.Address, port.Port, port.PID)
	}

	// Create a port watcher for the current process
	pw, err := portwatcher.New(os.Getpid(), callback)
	if err != nil {
		log.Fatal(err)
	}
	defer pw.Stop()

	// Start monitoring
	if err := pw.Start(); err != nil {
		log.Fatal(err)
	}

	// Start a TCP listener to trigger the callback
	listener, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		log.Fatal(err)
	}
	defer listener.Close()

	// Give the watcher time to detect the new port
	time.Sleep(2 * time.Second)

	// The callback will print something like:
	// New port detected: 127.0.0.1:12345 (PID: 4163)
}

func ExamplePortWatcher_childProcess() {
	// Create a callback to track ports from child processes
	portsChan := make(chan portwatcher.Port, 10)
	callback := func(port portwatcher.Port) {
		select {
		case portsChan <- port:
		default:
			// Channel full, drop the port
		}
	}

	// Monitor the current process and its children
	pw, err := portwatcher.New(os.Getpid(), callback)
	if err != nil {
		log.Fatal(err)
	}
	defer pw.Stop()

	if err := pw.Start(); err != nil {
		log.Fatal(err)
	}

	// In a real scenario, you would spawn child processes here
	// that might open ports

	// Process detected ports
	go func() {
		for port := range portsChan {
			fmt.Printf("Child process %d opened port %d\n", port.PID, port.Port)
		}
	}()

	// Keep monitoring for some time
	time.Sleep(10 * time.Second)
}