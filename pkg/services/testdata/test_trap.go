//go:build ignore
// +build ignore

package main

import (
	"os"
	"os/signal"
	"syscall"
	"time"
)

func main() {
	// Create a channel to listen for signals
	sigChan := make(chan os.Signal, 1)

	// Register the channel to receive SIGTERM
	signal.Notify(sigChan, syscall.SIGTERM)

	// Ignore SIGTERM by reading from the channel and doing nothing
	go func() {
		for range sigChan {
			// Ignore the signal - do nothing
		}
	}()

	// Keep the process running forever
	for {
		time.Sleep(1 * time.Second)
	}
}
