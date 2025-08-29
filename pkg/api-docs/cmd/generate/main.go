package main

import (
	"flag"
	"fmt"
	"log"
	"os"
	"os/exec"
	"path/filepath"

	apidocs "github.com/superfly/sprite-env/pkg/api-docs"
)

func main() {
	var (
		source      = flag.String("source", ".", "Source directory to scan for API documentation")
		output      = flag.String("output", "openapi.json", "Output file for OpenAPI specification")
		format      = flag.String("format", "json", "Output format: json or yaml")
		title       = flag.String("title", "Sprites API", "API title")
		version     = flag.String("version", "1.0.0", "API version")
		description = flag.String("description", "", "API description")
		serverURL   = flag.String("server", "http://localhost:8080", "Server URL")
		validate    = flag.Bool("validate", true, "Validate the generated spec with Redocly CLI")
	)

	flag.Parse()

	// Create generator
	generator := apidocs.NewGenerator(*title, *version)

	// Set description if provided
	if *description != "" {
		generator.SetDescription(*description)
	} else {
		generator.SetDescription("Sprites API provides a platform for running containerized workloads with integrated object storage.")
	}

	// Set license
	generator.SetLicense("MIT", "https://opensource.org/licenses/MIT")

	// Add server
	generator.AddServer(*serverURL, "Sprites API server")

	// Add security scheme
	generator.AddSecurityScheme("Bearer", apidocs.SecurityScheme{
		Type:        "http",
		Scheme:      "bearer",
		Description: "Bearer token authentication",
	})

	// Parse source directory
	log.Printf("Parsing source files in %s...", *source)
	if err := generator.ParseDirectory(*source); err != nil {
		log.Fatalf("Error parsing source files: %v", err)
	}

	// Generate spec
	spec := generator.Generate()

	// Create output directory if needed
	outputDir := filepath.Dir(*output)
	if err := os.MkdirAll(outputDir, 0755); err != nil {
		log.Fatalf("Error creating output directory: %v", err)
	}

	// Open output file
	file, err := os.Create(*output)
	if err != nil {
		log.Fatalf("Error creating output file: %v", err)
	}
	defer file.Close()

	// Write output
	switch *format {
	case "json":
		if err := generator.WriteJSON(file); err != nil {
			log.Fatalf("Error writing JSON: %v", err)
		}
	case "yaml":
		if err := generator.WriteYAML(file); err != nil {
			log.Fatalf("Error writing YAML: %v", err)
		}
	default:
		log.Fatalf("Unknown format: %s", *format)
	}

	log.Printf("OpenAPI specification written to %s", *output)

	// Print summary
	pathCount := len(spec.Paths)
	operationCount := 0
	for _, path := range spec.Paths {
		operationCount += len(path)
	}

	fmt.Printf("\nAPI Documentation Generated:\n")
	fmt.Printf("  Title: %s\n", spec.Info.Title)
	fmt.Printf("  Version: %s\n", spec.Info.Version)
	fmt.Printf("  Paths: %d\n", pathCount)
	fmt.Printf("  Operations: %d\n", operationCount)
	fmt.Printf("  Tags: %d\n", len(spec.Tags))
	fmt.Printf("  Schemas: %d\n", len(spec.Components.Schemas))

	// Validate with Redocly CLI if requested
	if *validate {
		fmt.Printf("\n🔍 Validating OpenAPI spec with Redocly CLI...\n")

		// Check if npx is available
		if _, err := exec.LookPath("npx"); err != nil {
			log.Printf("⚠️  Warning: npx not found in PATH, skipping validation")
			return
		}

		// Run Redocly CLI validation
		cmd := exec.Command("npx", "@redocly/cli@latest", "lint", *output)
		cmd.Stdout = os.Stdout
		cmd.Stderr = os.Stderr

		if err := cmd.Run(); err != nil {
			// Don't fail the generation, just warn
			log.Printf("⚠️  OpenAPI validation completed with warnings or errors")
		} else {
			fmt.Printf("✅ OpenAPI spec validation passed!\n")
		}
	}
}
