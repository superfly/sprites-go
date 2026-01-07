// Example: Get Network Policy
// Endpoint: GET /v1/sprites/{name}/policy/network
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

	policy, err := sprite.GetNetworkPolicy(context.Background())
	if err != nil {
		log.Fatal(err)
	}

	out, _ := json.MarshalIndent(policy, "", "  ")
	fmt.Println(string(out))
}
