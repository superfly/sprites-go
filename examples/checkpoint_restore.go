// Example: Restore Checkpoint
// Endpoint: POST /v1/sprites/{name}/checkpoints/{checkpoint_id}/restore
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

	stream, err := sprite.RestoreCheckpoint(context.Background(), checkpointID)
	if err != nil {
		log.Fatal(err)
	}

	err = stream.ProcessAll(func(msg *sprites.StreamMessage) error {
		out, _ := json.Marshal(msg)
		fmt.Println(string(out))
		return nil
	})
	if err != nil {
		log.Fatal(err)
	}
}
