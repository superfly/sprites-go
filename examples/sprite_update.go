// Example: Update Sprite
// Endpoint: PUT /v1/sprites/{name}
package main

import (
	"context"
	"fmt"
	"log"
	"os"

	sprites "github.com/superfly/sprites-go"
)

func main() {
	token := os.Getenv("SPRITE_TOKEN")
	spriteName := os.Getenv("SPRITE_NAME")

	client := sprites.New(token)

	err := client.UpdateSprite(context.Background(), spriteName, &sprites.UpdateSpriteRequest{
		URLSettings: &sprites.URLSettings{Auth: "public"},
		Labels:      []string{"prod"},
	})
	if err != nil {
		log.Fatal(err)
	}

	fmt.Println("Sprite updated")
}
