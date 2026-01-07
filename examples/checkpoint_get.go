// Example: Get Checkpoint
// Endpoint: GET /v1/sprites/{name}/checkpoints/{checkpoint_id}
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
	checkpointID := os.Getenv("CHECKPOINT_ID")
	if checkpointID == "" {
		checkpointID = "v1"
	}

	client := sprites.New(token)
	sprite := client.Sprite(spriteName)

	checkpoint, err := sprite.GetCheckpoint(context.Background(), checkpointID)
	if err != nil {
		log.Fatal(err)
	}

	out, _ := json.MarshalIndent(checkpoint, "", "  ")
	fmt.Println(string(out))
}
