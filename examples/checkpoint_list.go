// Example: List Checkpoints
// Endpoint: GET /v1/sprites/{name}/checkpoints
package main

import (
	"context"
	"encoding/json"
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

	checkpoints, err := sprite.ListCheckpoints(context.Background(), "")
	if err != nil {
		log.Fatal(err)
	}

	out, _ := json.MarshalIndent(checkpoints, "", "  ")
	fmt.Println(string(out))
}
