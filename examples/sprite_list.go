// Example: List Sprites
// Endpoint: GET /v1/sprites
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

	client := sprites.New(token)

	list, err := client.ListSprites(context.Background(), nil)
	if err != nil {
		log.Fatal(err)
	}

	out, _ := json.MarshalIndent(list.Sprites, "", "  ")
	fmt.Println(string(out))
}
