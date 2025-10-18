# Fly Package

Package `fly` provides utilities for interacting with the Fly.io local API socket.

## Features

- **LocalAPI Client**: HTTP client for making requests to the Fly local API socket (`/.fly/api`)
- **Suspend**: Suspend the current machine
- **Secrets API**: List and retrieve secrets

## Usage

### Suspending a Machine

```go
import (
    "context"
    "github.com/superfly/sprite-env/pkg/fly"
)

func main() {
    ctx := context.Background()
    err := fly.Suspend(ctx)
    if err != nil {
        log.Fatal(err)
    }
}
```

### Listing Secrets

```go
import (
    "context"
    "github.com/superfly/sprite-env/pkg/fly"
)

func main() {
    ctx := context.Background()

    // List all secrets
    secrets, err := fly.Secrets.List(ctx, "")
    if err != nil {
        log.Fatal(err)
    }

    for _, secret := range secrets {
        fmt.Printf("Secret: %s = %s\n", secret.Name, secret.Value)
    }
}
```

### Getting a Specific Secret

```go
import (
    "context"
    "github.com/superfly/sprite-env/pkg/fly"
)

func main() {
    ctx := context.Background()

    // Get a specific secret
    secret, err := fly.Secrets.Get(ctx, "MY_SECRET", "")
    if err != nil {
        log.Fatal(err)
    }

    fmt.Printf("Secret value: %s\n", secret.Value)
}
```

### Using the LocalAPI Client Directly

```go
import (
    "context"
    "github.com/superfly/sprite-env/pkg/fly"
)

func main() {
    ctx := context.Background()

    // Make a GET request
    resp, err := fly.LocalAPI.Get(ctx, "/v1/apps/my-app/machines")
    if err != nil {
        log.Fatal(err)
    }
    defer resp.Body.Close()

    // Process response...
}
```

## Testing

The package includes a mock server for testing:

```go
import (
    "testing"
    "github.com/superfly/sprite-env/pkg/fly"
)

func TestMyFunction(t *testing.T) {
    // Create and start mock server
    mock, err := fly.NewMockServer()
    if err != nil {
        t.Fatal(err)
    }
    defer mock.Stop()

    if err := mock.Start(); err != nil {
        t.Fatal(err)
    }

    // Add test secrets
    mock.SetSecret(fly.Secret{
        Name:  "TEST_SECRET",
        Value: "test-value",
    })

    // Override the socket path for testing
    originalPath := fly.LocalAPI.socketPath
    fly.LocalAPI.socketPath = mock.SocketPath()
    defer func() {
        fly.LocalAPI.socketPath = originalPath
    }()

    // Your test code here...
}
```

## Environment Variables

The package requires the following environment variables to be set:

- `FLY_APP_NAME`: The name of the Fly.io app
- `FLY_MACHINE_ID`: The ID of the current machine

## API Reference

### LocalAPI

- `Get(ctx, path)`: Perform a GET request
- `Head(ctx, path)`: Perform a HEAD request
- `Post(ctx, path, body)`: Perform a POST request
- `Do(ctx, method, path, body)`: Perform any HTTP request

### Suspend

```go
func Suspend(ctx context.Context) error
```

Suspends the current machine.

### Secrets API

```go
func (s *SecretsAPI) List(ctx context.Context, minVersion string) ([]Secret, error)
```

Lists all secrets for the current app.

Parameters:
- `minVersion`: Optional minimum version to filter secrets

```go
func (s *SecretsAPI) Get(ctx context.Context, key string, minVersion string) (*Secret, error)
```

Gets a specific secret by name.

Parameters:
- `key`: The name of the secret to retrieve
- `minVersion`: Optional minimum version to filter secrets

Both methods automatically set `show_secrets=true` to return secret values.
