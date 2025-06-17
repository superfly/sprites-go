# Sprite-env HTTP API Documentation

## Overview

The sprite-env server now includes an HTTP API server that allows remote command execution with authentication. The API server is activated using the `--listen` flag when starting the sprite-env server.

## Starting the API Server

To enable the API server, use the `--listen` flag when starting sprite-env:

```bash
./sprite-env --listen 0.0.0.0:8090 -components-dir /path/to/components -- /path/to/supervised-process
```

## Authentication

All API endpoints require authentication via the `fly-replay-src` header. The header must include a `state` key with the format:

- **API mode**: `state=api:<token>` - Access to checkpoint, restore, and exec endpoints
- **Proxy mode**: `state=proxy:<token>:<port>` - Proxy requests to internal services

The token value must match the `SPRITE_HTTP_API_TOKEN` environment variable. If this environment variable is not set, authentication is disabled (not recommended for production).

### Header Format

The `fly-replay-src` header can contain multiple semicolon-separated key-value pairs:
```
fly-replay-src: region=ord;state=api:mysecrettoken;app=myapp
```

Only the `state` key is used for authentication. Other keys are ignored.

### Examples

API mode authentication:
```bash
curl -X POST http://localhost:8090/checkpoint \
  -H "fly-replay-src: state=api:mysecrettoken" \
  -H "Content-Type: application/json" \
  -d '{"checkpoint_id": "checkpoint-123"}'
```

Proxy mode authentication:
```bash
# Proxy to service on port 3000
curl -X GET http://localhost:8090/health \
  -H "fly-replay-src: state=proxy:mysecrettoken:3000"
```

## API Endpoints (API Mode)

### POST /checkpoint

Initiates a checkpoint operation.

**Request:**
```json
{
  "checkpoint_id": "string"
}
```

**Response:**
- Status: 202 Accepted
```json
{
  "status": "checkpoint initiated",
  "checkpoint_id": "string"
}
```

### POST /restore

Initiates a restore operation.

**Request:**
```json
{
  "checkpoint_id": "string"  
}
```

**Response:**
- Status: 202 Accepted
```json
{
  "status": "restore initiated",
  "checkpoint_id": "string"
}
```

### POST /exec

Executes a command and streams the output.

**Request:**
```json
{
  "command": ["command", "arg1", "arg2"],
  "timeout": 30000000000  // nanoseconds, optional (default: 30s)
}
```

**Response:**
- Status: 200 OK
- Content-Type: application/x-ndjson

The response is a stream of newline-delimited JSON messages:

```json
{"type":"stdout","data":"output line","time":"2024-01-01T12:00:00Z"}
{"type":"stderr","data":"error line","time":"2024-01-01T12:00:01Z"}
{"type":"exit","exit_code":0,"time":"2024-01-01T12:00:02Z"}
```

## Proxy Mode

When using proxy mode authentication (`state=proxy:<token>:<port>`), all requests are proxied to the specified port on localhost. This allows external access to internal services with authentication.

### How it works

1. Include the target port in the authentication header: `state=proxy:mytoken:3000`
2. All HTTP requests are forwarded to `http://127.0.0.1:3000`
3. The original path, query parameters, headers, and body are preserved
4. Response headers and body are returned to the client

### Examples

```bash
# Proxy GET request to internal service on port 3000
curl -X GET http://localhost:8090/api/users \
  -H "fly-replay-src: state=proxy:mysecrettoken:3000"

# Proxy POST request with body
curl -X POST http://localhost:8090/api/users \
  -H "fly-replay-src: state=proxy:mysecrettoken:3000" \
  -H "Content-Type: application/json" \
  -d '{"name": "John Doe"}'
```

### Headers

The proxy automatically:
- Removes the `fly-replay-src` header before forwarding
- Adds `X-Forwarded-For`, `X-Forwarded-Proto`, and `X-Forwarded-Host` headers
- Preserves all other headers from the original request

### Error Handling

- **502 Bad Gateway**: Target service returned an error or closed connection
- **503 Service Unavailable**: Target service is not running on the specified port
- **504 Gateway Timeout**: Target service did not respond within timeout period

## Error Responses

All endpoints return appropriate HTTP status codes:

- **400 Bad Request**: Invalid request format or missing required fields
- **401 Unauthorized**: Missing or invalid authentication token  
- **404 Not Found**: Endpoint not available in the current mode
- **405 Method Not Allowed**: HTTP method not supported
- **500 Internal Server Error**: Server error during operation

Error responses include a plain text error message in the response body.

## Notes

- The checkpoint and restore endpoints trigger state transitions but do not wait for completion
- Operations may take significant time to complete
- Proxy mode allows only one target port per authentication - use different tokens for different services

## Future Enhancements

- **Proxy mode**: Will allow proxying requests to the supervised process (TODO)
- Additional endpoints for system management
- WebSocket support for real-time command execution