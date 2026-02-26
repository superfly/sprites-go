// Example: Create Service
// Endpoint: PUT /v1/sprites/{name}/services/{service_name}
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

	httpPort := 8000
	stream, err := sprite.CreateService(context.Background(), serviceName, &sprites.ServiceRequest{
		Cmd:      "python",
		Args:     []string{"-m", "http.server", "8000"},
		HTTPPort: &httpPort,
	})
	if err != nil {
		log.Fatal(err)
	}

	err = stream.ProcessAll(func(event *sprites.ServiceLogEvent) error {
		out, _ := json.Marshal(event)
		fmt.Println(string(out))
		return nil
	})
	if err != nil {
		log.Fatal(err)
	}
}
