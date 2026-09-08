package sprites

import (
	"context"
	"encoding/json"
	"io"
	"net/http"
	"net/http/httptest"
	"testing"
)

// captureCreateRequest runs a create against a stub server and returns the
// decoded request body it received.
func captureCreateRequest(t *testing.T, create func(c *Client) error) map[string]any {
	t.Helper()

	var body map[string]any

	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		raw, err := io.ReadAll(r.Body)
		if err != nil {
			t.Errorf("reading request body: %v", err)
		}
		if err := json.Unmarshal(raw, &body); err != nil {
			t.Errorf("decoding request body %q: %v", raw, err)
		}

		w.WriteHeader(http.StatusCreated)
		_, _ = w.Write([]byte(`{"name":"test-sprite"}`))
	}))
	defer srv.Close()

	if err := create(New("test-token", WithBaseURL(srv.URL))); err != nil {
		t.Fatalf("create: %v", err)
	}

	return body
}

func TestCreateSpriteWithOptionsSendsRuntime(t *testing.T) {
	body := captureCreateRequest(t, func(c *Client) error {
		_, err := c.CreateSpriteWithOptions(context.Background(), "test-sprite", CreateSpriteOptions{
			Runtime: "some-runtime",
		})
		return err
	})

	if got := body["runtime"]; got != "some-runtime" {
		t.Errorf("runtime = %v, want %q", got, "some-runtime")
	}
}

func TestCreateSpriteOmitsEmptyRuntime(t *testing.T) {
	// An explicit empty runtime would ask the API for a variant named "",
	// rather than for the default one, so the field has to disappear.
	body := captureCreateRequest(t, func(c *Client) error {
		_, err := c.CreateSprite(context.Background(), "test-sprite", nil)
		return err
	})

	if _, present := body["runtime"]; present {
		t.Errorf("runtime present in body %v, want it omitted", body)
	}
}

func TestCreateSpriteWithOrgStillCarriesItsArguments(t *testing.T) {
	body := captureCreateRequest(t, func(c *Client) error {
		_, err := c.CreateSpriteWithOrg(context.Background(), "test-sprite",
			&SpriteConfig{RamMB: 2048}, nil, []string{"a-label"})
		return err
	})

	config, ok := body["config"].(map[string]any)
	if !ok {
		t.Fatalf("config = %v, want an object", body["config"])
	}
	if got := config["ram_mb"]; got != float64(2048) {
		t.Errorf("config.ram_mb = %v, want 2048", got)
	}

	labels, ok := body["labels"].([]any)
	if !ok || len(labels) != 1 || labels[0] != "a-label" {
		t.Errorf("labels = %v, want [a-label]", body["labels"])
	}
}
