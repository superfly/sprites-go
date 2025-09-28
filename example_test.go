package sprites_test

import (
	"context"
	"fmt"
	"log"
	"time"

	sprites "github.com/superfly/sprites-go"
)

func ExampleClient_Sprite() {
	// Create a client with authentication
	client := sprites.New("your-auth-token", sprites.WithBaseURL("https://sprite.example.com"))

	// Get a sprite handle
	sprite := client.Sprite("my-sprite")

	// Run a simple command
	cmd := sprite.Command("echo", "hello", "world")
	output, err := cmd.Output()
	if err != nil {
		log.Fatal(err)
	}

	fmt.Printf("Output: %s", output)
	// Output would be: hello world
}

func ExampleSprite_Command() {
	client := sprites.New("your-auth-token")
	sprite := client.Sprite("my-sprite")

	// Create a command with pipes
	cmd := sprite.Command("grep", "pattern")

	// Get stdin pipe
	stdin, err := cmd.StdinPipe()
	if err != nil {
		log.Fatal(err)
	}

	// Get stdout pipe
	stdout, err := cmd.StdoutPipe()
	if err != nil {
		log.Fatal(err)
	}

	// Start the command
	if err := cmd.Start(); err != nil {
		log.Fatal(err)
	}

	// Write to stdin
	go func() {
		defer stdin.Close()
		fmt.Fprintln(stdin, "line with pattern")
		fmt.Fprintln(stdin, "line without")
		fmt.Fprintln(stdin, "another pattern line")
	}()

	// Read from stdout
	// In real code, you'd process the output
	_ = stdout

	// Wait for command to complete
	if err := cmd.Wait(); err != nil {
		log.Fatal(err)
	}
}

func ExampleSprite_CommandContext() {
	client := sprites.New("your-auth-token")
	sprite := client.Sprite("my-sprite")

	// Create a command with timeout
	ctx, cancel := context.WithTimeout(context.Background(), 30*time.Second)
	defer cancel()

	cmd := sprite.CommandContext(ctx, "long-running-command")
	err := cmd.Run()
	if err != nil {
		// Command will be killed if context times out
		log.Fatal(err)
	}
}

func Example_compatibleWithExecCmd() {
	// The sprite.Cmd API mirrors exec.Cmd

	// With exec.Cmd:
	// cmd := exec.Command("ls", "-la")
	// cmd.Dir = "/tmp"
	// cmd.Env = []string{"FOO=bar"}
	// output, err := cmd.Output()

	// With sprite SDK:
	client := sprites.New("your-auth-token")
	sprite := client.Sprite("my-sprite")

	cmd := sprite.Command("ls", "-la")
	cmd.Dir = "/tmp"
	cmd.Env = []string{"FOO=bar"}
	output, err := cmd.Output()

	if err != nil {
		log.Fatal(err)
	}

	fmt.Printf("Files: %s", output)
}
