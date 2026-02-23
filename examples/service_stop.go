// Example: Stop Service
// Endpoint: POST /v1/sprites/{name}/services/{service_name}/stop
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

	stream, err := sprite.StopService(context.Background(), serviceName)
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
