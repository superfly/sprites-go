// Example: List Services
// Endpoint: GET /v1/sprites/{name}/services
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

	services, err := sprite.ListServices(context.Background())
	if err != nil {
		log.Fatal(err)
	}

	out, _ := json.MarshalIndent(services, "", "  ")
	fmt.Println(string(out))
}
