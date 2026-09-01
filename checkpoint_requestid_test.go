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

var errStreamInterrupted = errors.New("stream interrupted")

type failingStreamBody struct{}

func (failingStreamBody) Read([]byte) (int, error) {
	return 0, errStreamInterrupted
}

func (failingStreamBody) Close() error {
	return nil
}

type streamRoundTripper struct {
	requestID string
	body      io.ReadCloser
}

func (rt streamRoundTripper) RoundTrip(*http.Request) (*http.Response, error) {
	return &http.Response{
		StatusCode: http.StatusOK,
		Header: hdr(map[string]string{
			"Fly-Request-Id": rt.requestID,
		}),
		Body: rt.body,
	}, nil
}

type messageStream interface {
	Next() (*StreamMessage, error)
	ProcessAll(func(*StreamMessage) error) error
}

func TestCheckpointAndRestoreStreamErrorsIncludeRequestID(t *testing.T) {
	const requestID = "01M19T3EMF8NHCPCPR0YN9ZRYW-lax"

	streamTypes := []struct {
		name string
		open func(*Client) (messageStream, error)
	}{
		{
			name: "checkpoint",
			open: func(client *Client) (messageStream, error) {
				return client.CreateCheckpoint(context.Background(), "test-sprite")
			},
		},
		{
			name: "restore",
			open: func(client *Client) (messageStream, error) {
				return client.RestoreCheckpoint(context.Background(), "test-sprite", "test-checkpoint")
			},
		},
	}

	operations := []struct {
		name string
		run  func(messageStream) error
	}{
		{
			name: "Next",
			run: func(stream messageStream) error {
				_, err := stream.Next()
				return err
			},
		},
		{
			name: "ProcessAll",
			run: func(stream messageStream) error {
				return stream.ProcessAll(func(*StreamMessage) error {
					return errors.New("handler called for a failed stream")
				})
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
			want: "failed to parse message",
		},
	}

	for _, streamType := range streamTypes {
		for _, operation := range operations {
			for _, failure := range failures {
				t.Run(streamType.name+"/"+operation.name+"/"+failure.name, func(t *testing.T) {
					client := New("test-token", WithHTTPClient(&http.Client{
						Transport: streamRoundTripper{requestID: requestID, body: failure.body()},
					}))
					stream, err := streamType.open(client)
					if err != nil {
						t.Fatalf("open stream: %v", err)
					}

					err = operation.run(stream)
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
}

func TestStreamErrorWithoutRequestIDIsUnchanged(t *testing.T) {
	streams := []struct {
		name   string
		stream messageStream
	}{
		{
			name: "checkpoint",
			stream: &CheckpointStream{
				reader:  failingStreamBody{},
				scanner: bufio.NewScanner(failingStreamBody{}),
			},
		},
		{
			name: "restore",
			stream: &RestoreStream{
				reader:  failingStreamBody{},
				scanner: bufio.NewScanner(failingStreamBody{}),
			},
		},
	}

	for _, tt := range streams {
		t.Run(tt.name, func(t *testing.T) {
			_, err := tt.stream.Next()
			if err != errStreamInterrupted {
				t.Fatalf("error = %v, want the original error", err)
			}
		})
	}
}

var _ io.ReadCloser = failingStreamBody{}
