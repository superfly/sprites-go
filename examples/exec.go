// Example: Execute Command
// Endpoint: WSS /v1/sprites/{name}/exec
package main

import (
	"fmt"
	"log"
	"os"

	sprites "github.com/superfly/sprites-go"
)

func main() {
	token := os.Getenv("SPRITE_TOKEN")
	spriteName := os.Getenv("SPRITE_NAME")

	client := sprites.New(token)
	sprite := client.Sprite(spriteName)

	cmd := sprite.Command("echo", "hello", "world")
	output, err := cmd.Output()
	if err != nil {
		log.Fatal(err)
	}

	fmt.Print(string(output))
}
