// Example: Get Service
// Endpoint: GET /v1/sprites/{name}/services/{service_name}
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
	serviceName := os.Getenv("SERVICE_NAME")

	client := sprites.New(token)
	sprite := client.Sprite(spriteName)

	service, err := sprite.GetService(context.Background(), serviceName)
	if err != nil {
		log.Fatal(err)
	}

	out, _ := json.MarshalIndent(service, "", "  ")
	fmt.Println(string(out))
}
