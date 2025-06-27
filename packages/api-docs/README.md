# API Docs Generator

This package generates OpenAPI 3.1 specifications from Go source code documentation comments.

## Usage

The generator parses specially formatted comments in Go source files to produce an OpenAPI specification. **Only endpoints marked with `@public` will be included in the generated documentation.**

### Command Line

```bash
go run cmd/generate/main.go \
  -source ./lib \
  -output ./openapi.json \
  -title "My API" \
  -version "1.0.0"
```

### Documentation Format

Add documentation comments to your HTTP handler functions. **Important: Only handlers with the `@public` directive will be included in the OpenAPI spec.**

```go
// @public
// @operation GET /users/{id}
// @summary Get user by ID  
// @description Retrieve detailed user information
// @tags Users
// @security Bearer
// @param id path string true "User ID"
// @response 200 {object} User "User details"
// @response 404 {string} string "User not found"
func handleGetUser(w http.ResponseWriter, r *http.Request) {
    // handler implementation
}
```

### Supported Directives

- `@public` - **Required** to include the endpoint in the OpenAPI spec
- `@operation METHOD /path` - Define the HTTP method and path
- `@summary` - Short description of the endpoint
- `@description` - Detailed description
- `@tags` - Comma-separated list of tags
- `@security` - Security scheme name (e.g., Bearer)
- `@param name in type required "description"` - Parameter definition
- `@body TypeName` - Request body type
- `@response code {type} TypeName "description"` - Response definition
- `@response.example code {"json": "example"}` - Response example

### Type Definitions

The generator automatically discovers and includes exported struct types from your source files:

```go
type CreateRequest struct {
    Name     string `json:"name"`
    Config   Config `json:"config"`
}
```

These will be included in the OpenAPI components/schemas section.

### Excluding Endpoints

Any endpoint without the `@public` directive will be excluded from the generated OpenAPI specification. This is useful for:
- Internal health check endpoints
- Admin-only endpoints
- Deprecated endpoints
- Any endpoint you don't want to expose in public documentation