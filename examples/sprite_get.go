// Example: Get Sprite
// Endpoint: GET /v1/sprites/{name}
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

	sprite, err := client.GetSprite(context.Background(), spriteName)
	if err != nil {
		log.Fatal(err)
	}

	out, _ := json.MarshalIndent(sprite, "", "  ")
	fmt.Println(string(out))
}
