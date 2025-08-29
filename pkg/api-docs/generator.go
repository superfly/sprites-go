package apidocs

import (
	"encoding/json"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"io"
	"os"
	"path/filepath"
	"regexp"
	"strings"
)

// OpenAPISpec represents the OpenAPI 3.1 specification
type OpenAPISpec struct {
	OpenAPI    string                          `json:"openapi"`
	Info       Info                            `json:"info"`
	Servers    []Server                        `json:"servers,omitempty"`
	Paths      map[string]map[string]Operation `json:"paths"`
	Components *Components                     `json:"components,omitempty"`
	Security   []SecurityRequirement           `json:"security,omitempty"`
	Tags       []Tag                           `json:"tags,omitempty"`
}

// Info represents API information
type Info struct {
	Title       string   `json:"title"`
	Description string   `json:"description,omitempty"`
	Version     string   `json:"version"`
	License     *License `json:"license,omitempty"`
}

// License represents API license information
type License struct {
	Name string `json:"name"`
	URL  string `json:"url,omitempty"`
}

// Server represents a server
type Server struct {
	URL         string                    `json:"url"`
	Description string                    `json:"description,omitempty"`
	Variables   map[string]ServerVariable `json:"variables,omitempty"`
}

// ServerVariable represents a server variable
type ServerVariable struct {
	Default     string   `json:"default"`
	Description string   `json:"description,omitempty"`
	Enum        []string `json:"enum,omitempty"`
}

// Operation represents an API operation
type Operation struct {
	Tags        []string              `json:"tags,omitempty"`
	Summary     string                `json:"summary,omitempty"`
	Description string                `json:"description,omitempty"`
	OperationID string                `json:"operationId,omitempty"`
	Parameters  []Parameter           `json:"parameters,omitempty"`
	RequestBody *RequestBody          `json:"requestBody,omitempty"`
	Responses   map[string]Response   `json:"responses"`
	Security    []map[string][]string `json:"security"`
}

// Parameter represents an API parameter
type Parameter struct {
	Name        string  `json:"name"`
	In          string  `json:"in"`
	Description string  `json:"description,omitempty"`
	Required    bool    `json:"required,omitempty"`
	Schema      *Schema `json:"schema"`
}

// RequestBody represents a request body
type RequestBody struct {
	Description string               `json:"description,omitempty"`
	Required    bool                 `json:"required,omitempty"`
	Content     map[string]MediaType `json:"content"`
}

// Response represents an API response
type Response struct {
	Description string               `json:"description"`
	Content     map[string]MediaType `json:"content,omitempty"`
	Headers     map[string]Header    `json:"headers,omitempty"`
}

// MediaType represents a media type
type MediaType struct {
	Schema   *Schema            `json:"schema,omitempty"`
	Example  interface{}        `json:"example,omitempty"`
	Examples map[string]Example `json:"examples,omitempty"`
}

// Schema represents a JSON schema
type Schema struct {
	Type        string             `json:"type,omitempty"`
	Format      string             `json:"format,omitempty"`
	Properties  map[string]*Schema `json:"properties,omitempty"`
	Items       *Schema            `json:"items,omitempty"`
	Required    []string           `json:"required,omitempty"`
	Description string             `json:"description,omitempty"`
	Ref         string             `json:"$ref,omitempty"`
	AllOf       []*Schema          `json:"allOf,omitempty"`
	OneOf       []*Schema          `json:"oneOf,omitempty"`
	AnyOf       []*Schema          `json:"anyOf,omitempty"`
	Enum        []interface{}      `json:"enum,omitempty"`
	Default     interface{}        `json:"default,omitempty"`
	Example     interface{}        `json:"example,omitempty"`
}

// Header represents a response header
type Header struct {
	Description string  `json:"description,omitempty"`
	Schema      *Schema `json:"schema"`
}

// Example represents an example
type Example struct {
	Summary     string      `json:"summary,omitempty"`
	Description string      `json:"description,omitempty"`
	Value       interface{} `json:"value"`
}

// Components represents reusable components
type Components struct {
	Schemas         map[string]*Schema        `json:"schemas,omitempty"`
	Responses       map[string]Response       `json:"responses,omitempty"`
	Parameters      map[string]Parameter      `json:"parameters,omitempty"`
	Examples        map[string]Example        `json:"examples,omitempty"`
	RequestBodies   map[string]RequestBody    `json:"requestBodies,omitempty"`
	Headers         map[string]Header         `json:"headers,omitempty"`
	SecuritySchemes map[string]SecurityScheme `json:"securitySchemes,omitempty"`
}

// SecurityScheme represents a security scheme
type SecurityScheme struct {
	Type        string `json:"type"`
	Description string `json:"description,omitempty"`
	Name        string `json:"name,omitempty"`
	In          string `json:"in,omitempty"`
	Scheme      string `json:"scheme,omitempty"`
}

// SecurityRequirement represents a security requirement
type SecurityRequirement map[string][]string

// Tag represents an API tag
type Tag struct {
	Name        string `json:"name"`
	Description string `json:"description,omitempty"`
}

// Generator generates OpenAPI documentation from Go source files
type Generator struct {
	spec        *OpenAPISpec
	typeSchemas map[string]*Schema
	tagMap      map[string]bool
}

// NewGenerator creates a new documentation generator
func NewGenerator(title, version string) *Generator {
	return &Generator{
		spec: &OpenAPISpec{
			OpenAPI: "3.1.0",
			Info: Info{
				Title:   title,
				Version: version,
			},
			Paths: make(map[string]map[string]Operation),
			Components: &Components{
				Schemas:         make(map[string]*Schema),
				SecuritySchemes: make(map[string]SecurityScheme),
			},
		},
		typeSchemas: make(map[string]*Schema),
		tagMap:      make(map[string]bool),
	}
}

// SetDescription sets the API description
func (g *Generator) SetDescription(description string) {
	g.spec.Info.Description = description
}

// SetLicense sets the API license
func (g *Generator) SetLicense(name, url string) {
	g.spec.Info.License = &License{
		Name: name,
		URL:  url,
	}
}

// AddServer adds a server to the spec
func (g *Generator) AddServer(url, description string) {
	g.spec.Servers = append(g.spec.Servers, Server{
		URL:         url,
		Description: description,
	})
}

// AddSecurityScheme adds a security scheme
func (g *Generator) AddSecurityScheme(name string, scheme SecurityScheme) {
	g.spec.Components.SecuritySchemes[name] = scheme
}

// ParseDirectory parses all Go files in a directory
func (g *Generator) ParseDirectory(dir string) error {
	return filepath.Walk(dir, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}

		if strings.HasSuffix(path, ".go") && !strings.HasSuffix(path, "_test.go") {
			if err := g.ParseFile(path); err != nil {
				return fmt.Errorf("error parsing %s: %w", path, err)
			}
		}

		return nil
	})
}

// ParseFile parses a single Go file for API documentation
func (g *Generator) ParseFile(filename string) error {
	fset := token.NewFileSet()
	src, err := os.ReadFile(filename)
	if err != nil {
		return err
	}

	file, err := parser.ParseFile(fset, filename, src, parser.ParseComments)
	if err != nil {
		return err
	}

	// Parse type definitions first
	for _, decl := range file.Decls {
		if genDecl, ok := decl.(*ast.GenDecl); ok && genDecl.Tok == token.TYPE {
			for _, spec := range genDecl.Specs {
				if typeSpec, ok := spec.(*ast.TypeSpec); ok {
					g.parseTypeDefinition(typeSpec, genDecl.Doc)
				}
			}
		}
	}

	// Parse function declarations for API endpoints
	for _, decl := range file.Decls {
		if fn, ok := decl.(*ast.FuncDecl); ok && fn.Doc != nil {
			g.parseFunctionDoc(fn)
		}
	}

	return nil
}

// parseFunctionDoc parses function documentation for API endpoints
func (g *Generator) parseFunctionDoc(fn *ast.FuncDecl) {
	docText := fn.Doc.Text()
	lines := strings.Split(docText, "\n")

	var operation *Operation
	var currentPath, currentMethod string
	var hasSecurityDefined bool
	var isPublic bool

	// First pass - check if this endpoint is marked as public
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "@public" {
			isPublic = true
			break
		}
	}

	// If not public, skip this function
	if !isPublic {
		return
	}

	// Second pass - parse the operation details
	for _, line := range lines {
		line = strings.TrimSpace(line)
		if line == "" || line == "@public" {
			continue
		}

		// Parse @operation directive
		if matches := regexp.MustCompile(`@operation\s+(\w+)\s+(.+)`).FindStringSubmatch(line); matches != nil {
			currentMethod = strings.ToLower(matches[1])
			currentPath = matches[2]
			operation = &Operation{
				Responses: make(map[string]Response),
			}
			hasSecurityDefined = false
			continue
		}

		if operation == nil {
			continue
		}

		// Check if security is defined
		if strings.Contains(line, "@security") {
			hasSecurityDefined = true
		}

		// Parse other directives
		g.parseDirective(line, operation)
	}

	// Add operation to spec
	if operation != nil && currentPath != "" && currentMethod != "" {
		// If no security was defined, add empty security array
		if !hasSecurityDefined {
			operation.Security = []map[string][]string{}
		}

		if g.spec.Paths[currentPath] == nil {
			g.spec.Paths[currentPath] = make(map[string]Operation)
		}

		// Generate operation ID
		if operation.OperationID == "" {
			operation.OperationID = fn.Name.Name
		}

		g.spec.Paths[currentPath][currentMethod] = *operation

		// Collect tags
		for _, tag := range operation.Tags {
			g.tagMap[tag] = true
		}
	}
}

// parseDirective parses a documentation directive
func (g *Generator) parseDirective(line string, operation *Operation) {
	// @summary
	if matches := regexp.MustCompile(`@summary\s+(.+)`).FindStringSubmatch(line); matches != nil {
		operation.Summary = matches[1]
		return
	}

	// @description
	if matches := regexp.MustCompile(`@description\s+(.+)`).FindStringSubmatch(line); matches != nil {
		operation.Description = matches[1]
		return
	}

	// @tags
	if matches := regexp.MustCompile(`@tags\s+(.+)`).FindStringSubmatch(line); matches != nil {
		tags := strings.Split(matches[1], ",")
		for i, tag := range tags {
			tags[i] = strings.TrimSpace(tag)
		}
		operation.Tags = tags
		return
	}

	// @security
	if matches := regexp.MustCompile(`@security\s+(.+)`).FindStringSubmatch(line); matches != nil {
		security := make(map[string][]string)
		security[matches[1]] = []string{}
		operation.Security = append(operation.Security, security)
		return
	}

	// @param
	if matches := regexp.MustCompile(`@param\s+(\w+)\s+(\w+)\s+(\w+)\s+(\w+)\s+"?([^"]*)"?`).FindStringSubmatch(line); matches != nil {
		param := Parameter{
			Name:        matches[1],
			In:          matches[2],
			Required:    matches[4] == "true",
			Description: matches[5],
			Schema:      g.parseTypeString(matches[3]),
		}
		operation.Parameters = append(operation.Parameters, param)
		return
	}

	// @body
	if matches := regexp.MustCompile(`@body\s+(.+)`).FindStringSubmatch(line); matches != nil {
		schema := g.getSchemaForType(matches[1])
		operation.RequestBody = &RequestBody{
			Required: true,
			Content: map[string]MediaType{
				"application/json": {
					Schema: schema,
				},
			},
		}
		return
	}

	// @response
	if matches := regexp.MustCompile(`@response\s+(\d+)\s+(\{[^}]+\})\s+(.+)\s+"([^"]+)"`).FindStringSubmatch(line); matches != nil {
		g.parseResponse(matches, operation)
		return
	}

	// @response without description
	if matches := regexp.MustCompile(`@response\s+(\d+)\s+"([^"]+)"`).FindStringSubmatch(line); matches != nil {
		operation.Responses[matches[1]] = Response{
			Description: matches[2],
		}
		return
	}

	// @response.example
	if matches := regexp.MustCompile(`@response\.example\s+(\d+)\s+(.+)`).FindStringSubmatch(line); matches != nil {
		code := matches[1]
		exampleJSON := matches[2]

		if resp, ok := operation.Responses[code]; ok {
			var example interface{}
			if err := json.Unmarshal([]byte(exampleJSON), &example); err == nil {
				if resp.Content == nil {
					resp.Content = make(map[string]MediaType)
				}
				if _, ok := resp.Content["application/json"]; !ok {
					resp.Content["application/json"] = MediaType{}
				}
				mediaType := resp.Content["application/json"]
				mediaType.Example = example
				resp.Content["application/json"] = mediaType
				operation.Responses[code] = resp
			}
		}
		return
	}
}

// parseResponse parses a response directive
func (g *Generator) parseResponse(matches []string, operation *Operation) {
	code := matches[1]
	typeStr := matches[2]
	typeName := matches[3]
	description := matches[4]

	var schema *Schema
	if typeStr == "{object}" {
		schema = g.getSchemaForType(typeName)
	} else if typeStr == "{string}" {
		schema = &Schema{Type: "string"}
	} else if typeStr == "{array}" {
		// For array types, we need to handle []package.Type syntax
		// getSchemaForType will handle this correctly
		schema = g.getSchemaForType(typeName)
	}

	response := Response{
		Description: description,
	}

	if schema != nil {
		response.Content = map[string]MediaType{
			"application/json": {
				Schema: schema,
			},
		}
	}

	operation.Responses[code] = response
}

// getSchemaForType gets or creates a schema for a type
func (g *Generator) getSchemaForType(typeName string) *Schema {
	// Handle inline object definitions like object{field=type}
	if strings.HasPrefix(typeName, "object{") && strings.HasSuffix(typeName, "}") {
		return g.parseInlineObject(typeName)
	}

	// Handle array types
	if strings.HasPrefix(typeName, "[]") {
		itemType := strings.TrimPrefix(typeName, "[]")
		return &Schema{
			Type:  "array",
			Items: g.getSchemaForType(itemType),
		}
	}

	// Strip package prefix from type names
	cleanTypeName := typeName
	if idx := strings.LastIndex(typeName, "."); idx != -1 {
		cleanTypeName = typeName[idx+1:]
	}

	// Check if it's a known type
	if _, ok := g.typeSchemas[cleanTypeName]; ok {
		return &Schema{Ref: "#/components/schemas/" + cleanTypeName}
	}

	// Handle primitive types
	return g.parseTypeString(cleanTypeName)
}

// parseInlineObject parses inline object definitions
func (g *Generator) parseInlineObject(objStr string) *Schema {
	// Extract content between braces
	content := strings.TrimPrefix(strings.TrimSuffix(objStr, "}"), "object{")

	schema := &Schema{
		Type:       "object",
		Properties: make(map[string]*Schema),
	}

	// Parse field definitions
	fields := strings.Split(content, ",")
	for _, field := range fields {
		parts := strings.Split(strings.TrimSpace(field), "=")
		if len(parts) == 2 {
			fieldName := strings.TrimSpace(parts[0])
			fieldType := strings.TrimSpace(parts[1])
			// Use getSchemaForType to handle complex types like arrays and packages
			schema.Properties[fieldName] = g.getSchemaForType(fieldType)
		}
	}

	return schema
}

// parseTypeString parses a type string and returns a schema
func (g *Generator) parseTypeString(typeStr string) *Schema {
	switch typeStr {
	case "string":
		return &Schema{Type: "string"}
	case "integer", "int", "int32":
		return &Schema{Type: "integer", Format: "int32"}
	case "int64":
		return &Schema{Type: "integer", Format: "int64"}
	case "float", "float32":
		return &Schema{Type: "number", Format: "float"}
	case "float64", "double":
		return &Schema{Type: "number", Format: "double"}
	case "boolean", "bool":
		return &Schema{Type: "boolean"}
	case "any":
		return &Schema{} // No type specified means any
	default:
		// Assume it's a reference to a schema
		return &Schema{Ref: "#/components/schemas/" + typeStr}
	}
}

// parseTypeDefinition parses a type definition
func (g *Generator) parseTypeDefinition(typeSpec *ast.TypeSpec, doc *ast.CommentGroup) {
	typeName := typeSpec.Name.Name

	// Skip private types
	if !ast.IsExported(typeName) {
		return
	}

	// Parse struct types
	if structType, ok := typeSpec.Type.(*ast.StructType); ok {
		schema := g.parseStructType(structType)
		g.typeSchemas[typeName] = schema
		g.spec.Components.Schemas[typeName] = schema
	}
}

// parseStructType parses a struct type into a schema
func (g *Generator) parseStructType(structType *ast.StructType) *Schema {
	schema := &Schema{
		Type:       "object",
		Properties: make(map[string]*Schema),
		Required:   []string{},
	}

	for _, field := range structType.Fields.List {
		if len(field.Names) == 0 {
			continue // Skip embedded fields for now
		}

		fieldName := field.Names[0].Name
		if !ast.IsExported(fieldName) {
			continue // Skip private fields
		}

		// Get JSON tag
		jsonName := fieldName
		if field.Tag != nil {
			tag := field.Tag.Value
			jsonTag := getJSONTag(tag)
			if jsonTag == "-" {
				continue // Skip fields with json:"-"
			}
			if jsonTag != "" {
				parts := strings.Split(jsonTag, ",")
				jsonName = parts[0]

				// Check if omitempty
				if !contains(parts[1:], "omitempty") {
					schema.Required = append(schema.Required, jsonName)
				}
			}
		}

		// Parse field type
		fieldSchema := g.parseFieldType(field.Type)
		schema.Properties[jsonName] = fieldSchema
	}

	return schema
}

// parseFieldType parses a field type into a schema
func (g *Generator) parseFieldType(expr ast.Expr) *Schema {
	switch t := expr.(type) {
	case *ast.Ident:
		return g.parseTypeString(t.Name)
	case *ast.StarExpr:
		// Pointer type - parse the underlying type
		return g.parseFieldType(t.X)
	case *ast.ArrayType:
		return &Schema{
			Type:  "array",
			Items: g.parseFieldType(t.Elt),
		}
	case *ast.MapType:
		// For simplicity, treat maps as objects with additional properties
		return &Schema{
			Type: "object",
		}
	case *ast.SelectorExpr:
		// Package.Type reference
		if ident, ok := t.X.(*ast.Ident); ok {
			pkgName := ident.Name
			typeName := t.Sel.Name

			// Special handling for common types
			if pkgName == "time" && typeName == "Time" {
				return &Schema{
					Type:   "string",
					Format: "date-time",
				}
			}

			// For other types, just use the type name without package
			return g.getSchemaForType(typeName)
		}
	}

	// Default to string for unknown types
	return &Schema{Type: "string"}
}

// getJSONTag extracts the JSON tag from a struct tag
func getJSONTag(tag string) string {
	// Remove backticks
	tag = strings.Trim(tag, "`")

	// Find json tag
	re := regexp.MustCompile(`json:"([^"]*)"`)
	matches := re.FindStringSubmatch(tag)
	if len(matches) > 1 {
		return matches[1]
	}

	return ""
}

// contains checks if a slice contains a string
func contains(slice []string, str string) bool {
	for _, s := range slice {
		if s == str {
			return true
		}
	}
	return false
}

// Generate generates the OpenAPI specification
func (g *Generator) Generate() *OpenAPISpec {
	// Add collected tags with descriptions
	tagDescriptions := map[string]string{
		"Health":        "Health check endpoints",
		"Documentation": "API documentation endpoints",
		"Organization":  "Organization management endpoints",
		"Sprites":       "Sprite management endpoints",
	}

	for tag := range g.tagMap {
		description := tagDescriptions[tag]
		if description == "" {
			description = tag + " endpoints"
		}
		g.spec.Tags = append(g.spec.Tags, Tag{
			Name:        tag,
			Description: description,
		})
	}

	// Clean up unused schemas
	usedSchemas := make(map[string]bool)

	// Mark schemas used in operations
	for _, pathOps := range g.spec.Paths {
		for _, op := range pathOps {
			g.markUsedSchemas(op, usedSchemas)
		}
	}

	// Mark schemas used by other schemas
	for _, schema := range g.spec.Components.Schemas {
		g.markUsedSchemasInSchema(schema, usedSchemas)
	}

	// Remove unused schemas
	for schemaName := range g.spec.Components.Schemas {
		if !usedSchemas[schemaName] {
			delete(g.spec.Components.Schemas, schemaName)
		}
	}

	return g.spec
}

// markUsedSchemas marks schemas used in an operation
func (g *Generator) markUsedSchemas(op Operation, used map[string]bool) {
	// Check request body
	if op.RequestBody != nil {
		for _, media := range op.RequestBody.Content {
			if media.Schema != nil {
				g.markSchemaRef(media.Schema, used)
			}
		}
	}

	// Check responses
	for _, resp := range op.Responses {
		for _, media := range resp.Content {
			if media.Schema != nil {
				g.markSchemaRef(media.Schema, used)
			}
		}
	}
}

// markSchemaRef marks a schema reference as used
func (g *Generator) markSchemaRef(schema *Schema, used map[string]bool) {
	if schema.Ref != "" {
		// Extract schema name from reference
		parts := strings.Split(schema.Ref, "/")
		if len(parts) > 0 {
			schemaName := parts[len(parts)-1]
			used[schemaName] = true
		}
	}

	// Check properties
	for _, prop := range schema.Properties {
		g.markSchemaRef(prop, used)
	}

	// Check array items
	if schema.Items != nil {
		g.markSchemaRef(schema.Items, used)
	}
}

// markUsedSchemasInSchema marks schemas referenced by another schema
func (g *Generator) markUsedSchemasInSchema(schema *Schema, used map[string]bool) {
	// Check properties
	for _, prop := range schema.Properties {
		g.markSchemaRef(prop, used)
	}

	// Check array items
	if schema.Items != nil {
		g.markSchemaRef(schema.Items, used)
	}
}

// WriteJSON writes the spec as JSON
func (g *Generator) WriteJSON(w io.Writer) error {
	encoder := json.NewEncoder(w)
	encoder.SetIndent("", "  ")
	return encoder.Encode(g.spec)
}

// WriteYAML writes the spec as YAML (simple implementation)
func (g *Generator) WriteYAML(w io.Writer) error {
	// For now, we'll just write JSON
	// A full YAML implementation would require a YAML library
	return g.WriteJSON(w)
}
