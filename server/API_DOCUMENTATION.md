# Sprite Environment HTTP API Documentation

This document describes the HTTP API endpoints available for managing the Sprite environment.

## Base URL

The API is served on port 8181 by default. All endpoints are relative to:
```
http://localhost:8181
```

## Authentication

The API requires authentication using the `SPRITE_HTTP_API_TOKEN` environment variable. You can authenticate using either of these methods:

### Method 1: Authorization Header (Recommended)
Include a Bearer token in the Authorization header:
```
Authorization: Bearer mysecrettoken
```

### Method 2: fly-replay-src Header
Include the token in the `fly-replay-src` header with the format:
```
fly-replay-src: state=api:mysecrettoken
```

The `fly-replay-src` header can contain multiple semicolon-separated key-value pairs:
```
fly-replay-src: region=ord;state=api:mysecrettoken;app=myapp
```

### Example Requests

Using Authorization header:
```bash
curl -X POST http://localhost:8181/exec \
  -H "Authorization: Bearer mysecrettoken" \
  -H "Content-Type: application/json" \
  -d '{"command": ["ls", "-la"]}'
```

Using fly-replay-src header:
```bash
curl -X POST http://localhost:8181/exec \
  -H "fly-replay-src: state=api:mysecrettoken" \
  -H "Content-Type: application/json" \
  -d '{"command": ["ls", "-la"]}'
```

## Endpoints

### 1. Execute Command - `/exec`

Execute a command within the Sprite environment.

**Method:** `POST`

**Request Body:**
```json
{
  "command": ["ls", "-la"],
  "env": {
    "KEY": "value"
  },
  "working_dir": "/app",
  "timeout": 30000000000,
  "tty": false
}
```

**Fields:**
- `command` (required): Array of command and arguments
- `env` (optional): Environment variables as key-value pairs
- `working_dir` (optional): Working directory for the command
- `timeout` (optional): Command timeout in nanoseconds (default: 30 seconds)
- `tty` (optional): Whether to allocate a pseudo-TTY (default: false)

**Response:** Server-Sent Events (SSE) stream with the following event types:
- `stdout`: Standard output data
- `stderr`: Standard error data
- `exit`: Command exit status
- `error`: Execution errors

**Example:**
```bash
curl -X POST http://localhost:8181/exec \
  -H "Authorization: Bearer mysecrettoken" \
  -H "Content-Type: application/json" \
  -d '{"command": ["echo", "hello world"]}'
```

### 2. Request Checkpoint - `/checkpoint`

Request a checkpoint of the current system state.

**Method:** `POST`

**Request Body:**
```json
{
  "checkpoint_id": "checkpoint-123"
}
```

**Response:**
```json
{
  "status": "checkpoint requested",
  "checkpoint_id": "checkpoint-123"
}
```

### 3. Request Restore - `/restore`

Request restoration from a checkpoint.

**Method:** `POST`

**Request Body:**
```json
{
  "checkpoint_id": "checkpoint-123"
}
```

**Response:**
```json
{
  "status": "restore requested",
  "checkpoint_id": "checkpoint-123"
}
```

### 4. CONNECT Proxy - `/proxy`

A restricted CONNECT proxy that allows tunneling to local ports only.

**Method:** `CONNECT`

**Usage:**
The proxy endpoint accepts standard HTTP CONNECT requests and establishes a tunnel to the specified port on localhost (127.0.0.1). Regardless of the hostname in the CONNECT request, all connections are made to 127.0.0.1.

**Example using curl:**
```bash
# Connect to a local service on port 3000
curl -x http://localhost:8181/proxy \
  -H "Authorization: Bearer mysecrettoken" \
  http://example.com:3000
```

**Example CONNECT request:**
```
CONNECT example.com:3000 HTTP/1.1
Host: example.com:3000
Authorization: Bearer mysecrettoken
```

**Response:**
```
HTTP/1.1 200 Connection Established
```

After receiving a 200 response, the connection becomes a bidirectional tunnel to `127.0.0.1:3000`.

**Notes:**
- Only the port number from the CONNECT request is used
- All connections are made to 127.0.0.1 regardless of the requested hostname
- The proxy respects the API's wait-for-running behavior

## Wait-for-Running Behavior

The `/exec` and `/proxy` endpoints will wait up to 30 seconds (configurable) for the system to reach the "Running" state before processing requests. This ensures commands are not executed before the system is ready.

Other endpoints (`/checkpoint`, `/restore`) do not wait and can be called during system startup.

## Error Responses

All endpoints return appropriate HTTP status codes:

- `200 OK`: Successful request
- `202 Accepted`: Request accepted (for checkpoint/restore)
- `400 Bad Request`: Invalid request format or parameters
- `401 Unauthorized`: Missing or invalid authentication
- `405 Method Not Allowed`: Wrong HTTP method
- `503 Service Unavailable`: System not ready (after timeout)

Error responses include a plain text error message in the response body.