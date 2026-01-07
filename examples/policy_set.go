// Example: Set Network Policy
// Endpoint: POST /v1/sprites/{name}/policy/network
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
	sprite := client.Sprite(spriteName)

	policy := &sprites.NetworkPolicy{
		Rules: []sprites.NetworkPolicyRule{
			{Domain: "api.github.com", Action: "allow"},
			{Domain: "*.npmjs.org", Action: "allow"},
		},
	}

	err := sprite.UpdateNetworkPolicy(context.Background(), policy)
	if err != nil {
		log.Fatal(err)
	}

	fmt.Println("Network policy updated")
}
