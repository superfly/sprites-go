# Token handling in `cmd/deploy.go`

This document explains how the Fly API token is acquired and used in `cmd/deploy.go`.

## 1. Token acquisition

```go
// Get Fly API token
token := os.Getenv("FLY_API_TOKEN")
if token == "" {
    // Try to get token from flyctl
    cmd := exec.Command("flyctl", "auth", "token")
    output, err := cmd.Output()
    if err != nil {
        log.Fatal("FLY_API_TOKEN not set and couldn't get from flyctl: ", err)
    }
    token = strings.TrimSpace(string(output))
}
```
(see `cmd/deploy.go`, lines 77–86)

## 2. Passing token to the flaps client

```go
flapsClient, err := flaps.NewWithOptions(ctx, flaps.NewClientOpts{
    AppName: appName,
    Tokens:  tokens.Parse(token),
})
if err != nil {
    log.Fatal("Failed to create flaps client: ", err)
}
```
(see `cmd/deploy.go`, lines 124–130)

## 3. Relevant imports

```go
import (
    // ...
    "github.com/superfly/fly-go/flaps"
    "github.com/superfly/fly-go/tokens"
)
```
(see `cmd/deploy.go`, lines 15–17)