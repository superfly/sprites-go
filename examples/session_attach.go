// Example: Attach to Session
// Endpoint: WSS /v1/sprites/{name}/exec/{session_id}
package main

import (
	"context"
	"fmt"
	"io"
	"os"
	"strings"
	"time"

	sprites "github.com/superfly/sprites-go"
)

func main() {
	token := os.Getenv("SPRITE_TOKEN")
	spriteName := os.Getenv("SPRITE_NAME")

	client := sprites.New(token)
	sprite := client.Sprite(spriteName)

	// Find the session from exec example
	sessions, _ := sprite.ListSessions(context.Background())
	var targetSession *sprites.Session
	for _, s := range sessions {
		if strings.Contains(s.Command, "time.sleep") || strings.Contains(s.Command, "python") {
			targetSession = s
			break
		}
	}

	if targetSession == nil {
		fmt.Println("No running session found")
		os.Exit(1)
	}

	fmt.Printf("Attaching to session %s...\n", targetSession.ID)

	// Attach and read buffered output (includes data from before we connected)
	cmd := sprite.AttachSession(targetSession.ID)
	stdout, _ := cmd.StdoutPipe()
	cmd.Start()

	// Read for 2 seconds then disconnect
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
