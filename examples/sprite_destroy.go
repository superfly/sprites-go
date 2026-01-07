// Example: Destroy Sprite
// Endpoint: DELETE /v1/sprites/{name}
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

	err := client.DestroySprite(context.Background(), spriteName)
	if err != nil {
		log.Fatal(err)
	}

	fmt.Printf("Sprite '%s' destroyed\n", spriteName)
}
