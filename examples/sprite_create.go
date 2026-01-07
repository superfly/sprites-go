// Example: Create Sprite
// Endpoint: POST /v1/sprites
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

	_, err := client.CreateSprite(context.Background(), spriteName, nil)
	if err != nil {
		log.Fatal(err)
	}

	fmt.Printf("Sprite '%s' created\n", spriteName)
}
