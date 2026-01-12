// Example: Quick Start
// Endpoint: quickstart
package main

import (
	"context"
	"fmt"
	"os"

	sprites "github.com/superfly/sprites-go"
)

func main() {
	ctx := context.Background()

	// step: Install
	// go get github.com/superfly/sprites-go

	// step: Setup client
	client := sprites.New(os.Getenv("SPRITE_TOKEN"))

	// step: Create a sprite
	client.CreateSprite(ctx, os.Getenv("SPRITE_NAME"), nil)

	// step: Run Python
	output, _ := client.Sprite(os.Getenv("SPRITE_NAME")).Command("python", "-c", "print(2+2)").Output()
	fmt.Print(string(output))

	// step: Clean up
	client.DestroySprite(ctx, os.Getenv("SPRITE_NAME"))
}
