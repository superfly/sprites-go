// Example: Execute Command
// Endpoint: WSS /v1/sprites/{name}/exec
package main

import (
	"fmt"
	"io"
	"os"
	"time"

	sprites "github.com/superfly/sprites-go"
)

func main() {
	token := os.Getenv("SPRITE_TOKEN")
	spriteName := os.Getenv("SPRITE_NAME")

	client := sprites.New(token)
	sprite := client.Sprite(spriteName)

	// Start a command that runs for 30s (TTY sessions stay alive after disconnect)
	cmd := sprite.Command("python", "-c",
		"import time; print('Server ready on port 8080', flush=True); time.sleep(30)")
	cmd.SetTTY(true) // TTY sessions are detachable

	stdout, _ := cmd.StdoutPipe()
	cmd.Start()

	// Read for 2 seconds then disconnect (session keeps running)
	done := make(chan bool)
	go func() {
		buf := make([]byte, 1024)
		for {
			n, err := stdout.Read(buf)
			if n > 0 {
				fmt.Print(string(buf[:n]))
			}
			if err == io.EOF {
				break
			}
		}
		done <- true
	}()

	select {
	case <-done:
	case <-time.After(2 * time.Second):
	}
}
