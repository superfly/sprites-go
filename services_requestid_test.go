package sprites

import (
	"bufio"
	"context"
	"errors"
	"io"
	"net/http"
	"strings"
	"testing"
)

func TestServiceStreamErrorsIncludeRequestID(t *testing.T) {
	const requestID = "01M19T3EMF8NHCPCPR0YN9ZRYW-ord"

	operations := []struct {
		name string
		open func(*Client) (*ServiceStream, error)
	}{
		{
			name: "create",
			open: func(client *Client) (*ServiceStream, error) {
				return client.CreateService(context.Background(), "test-sprite", "test-service", &ServiceRequest{})
			},
		},
		{
			name: "start",
			open: func(client *Client) (*ServiceStream, error) {
				return client.StartService(context.Background(), "test-sprite", "test-service")
			},
		},
		{
			name: "stop",
			open: func(client *Client) (*ServiceStream, error) {
				return client.StopService(context.Background(), "test-sprite", "test-service")
			},
		},
	}
	failures := []struct {
		name string
		body func() io.ReadCloser
		want string
	}{
		{
			name: "read error",
			body: func() io.ReadCloser { return failingStreamBody{} },
			want: errStreamInterrupted.Error(),
		},
		{
			name: "truncated JSON",
			body: func() io.ReadCloser { return io.NopCloser(strings.NewReader(`{"type":`)) },
			want: "failed to parse service log event",
		},
	}

	for _, operation := range operations {
		for _, failure := range failures {
			t.Run(operation.name+"/"+failure.name, func(t *testing.T) {
				client := New("test-token", WithHTTPClient(&http.Client{
					Transport: streamRoundTripper{requestID: requestID, body: failure.body()},
				}))
				stream, err := operation.open(client)
				if err != nil {
					t.Fatalf("open stream: %v", err)
				}

				_, err = stream.Next()
				if !strings.Contains(err.Error(), failure.want) {
					t.Fatalf("error = %q, want text %q", err, failure.want)
				}
				if failure.name == "read error" && !errors.Is(err, errStreamInterrupted) {
					t.Fatalf("error = %v, want wrapped stream error", err)
				}
				if !strings.Contains(err.Error(), "fly-request-id: "+requestID) {
					t.Fatalf("request ID not surfaced: %q", err)
				}
			})
		}
	}
}

func TestServiceStreamErrorWithoutRequestIDIsUnchanged(t *testing.T) {
	stream := &ServiceStream{
		reader:  failingStreamBody{},
		scanner: bufio.NewScanner(failingStreamBody{}),
	}

	_, err := stream.Next()
	if err != errStreamInterrupted {
		t.Fatalf("error = %v, want the original error", err)
	}
}
