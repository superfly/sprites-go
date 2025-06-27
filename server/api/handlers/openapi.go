package handlers

import (
	_ "embed"
	"net/http"
)

//go:embed static/openapi.json
var openAPISpec []byte

// HandleOpenAPISpec serves the OpenAPI specification
// @public
// @operation GET /v1/openapi.json
// @summary Get OpenAPI specification
// @description Retrieve the OpenAPI 3.1 specification for the Sprites API
// @tags Documentation
// @response 200 {object} string "OpenAPI specification"
// @response 404 {string} string "OpenAPI specification not found"
func (h *Handlers) HandleOpenAPISpec(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.Header().Set("Access-Control-Allow-Origin", "*") // Allow CORS for docs tools
	w.Write(openAPISpec)
}
