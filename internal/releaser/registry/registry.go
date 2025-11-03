package registry

import (
	"context"
	"fmt"
	"net/url"
	"strings"

	"github.com/google/go-containerregistry/pkg/authn"
	"github.com/google/go-containerregistry/pkg/name"
	"github.com/google/go-containerregistry/pkg/v1/remote"
)

type Client struct {
	host string
	repo string // optional, when constructed with NewFromFQRepo
}

func New(host string) *Client {
	return &Client{host: host}
}

func NewFromFQRepo(fq string) *Client {
	// Expect fq form: host/owner/name
	parts := strings.SplitN(fq, "/", 2)
	if len(parts) != 2 {
		return &Client{host: "ghcr.io", repo: fq}
	}
	return &Client{host: parts[0], repo: parts[1]}
}

func (c *Client) ref(repo, tag string) (name.Reference, error) {
	if c.repo != "" {
		repo = c.repo
	}
	refStr := fmt.Sprintf("%s/%s:%s", c.host, repo, tag)
	return name.ParseReference(refStr)
}

func (c *Client) ImageExists(ctx context.Context, repo, tag string) (bool, error) {
	ref, err := c.ref(repo, tag)
	if err != nil {
		return false, err
	}
	// Anonymous auth works for public images on GHCR
	_, err = remote.Index(ref, remote.WithAuthFromKeychain(authn.DefaultKeychain))
	if err == nil {
		return true, nil
	}
	// If it's not a manifest list, try image
	_, imgErr := remote.Image(ref, remote.WithAuthFromKeychain(authn.DefaultKeychain))
	if imgErr == nil {
		return true, nil
	}
	// Return false for known 404-ish errors
	if strings.Contains(err.Error(), "MANIFEST_UNKNOWN") || strings.Contains(err.Error(), "unexpected status code 404") {
		return false, nil
	}
	if strings.Contains(imgErr.Error(), "MANIFEST_UNKNOWN") || strings.Contains(imgErr.Error(), "unexpected status code 404") {
		return false, nil
	}
	return false, err
}

func (c *Client) CopyTag(ctx context.Context, sourceTag, targetTag string) error {
	repo := c.repo
	if repo == "" {
		return fmt.Errorf("CopyTag requires client with repo set; use NewFromFQRepo")
	}
	srcRef, err := c.ref(repo, sourceTag)
	if err != nil {
		return err
	}
	tgtRef, err := c.ref(repo, targetTag)
	if err != nil {
		return err
	}
	idx, err := remote.Index(srcRef, remote.WithAuthFromKeychain(authn.DefaultKeychain))
	if err != nil {
		// Try single-arch fallback
		img, imgErr := remote.Image(srcRef, remote.WithAuthFromKeychain(authn.DefaultKeychain))
		if imgErr != nil {
			return err
		}
		return remote.Write(tgtRef, img, remote.WithAuthFromKeychain(authn.DefaultKeychain))
	}
	return remote.WriteIndex(tgtRef, idx, remote.WithAuthFromKeychain(authn.DefaultKeychain))
}

func (c *Client) Host() string { return c.host }

// NormalizeEndpoint ensures a valid URL for S3-like endpoints.
func NormalizeEndpoint(ep string) (string, error) {
	if ep == "" {
		return ep, nil
	}
	u, err := url.Parse(ep)
	if err != nil {
		return "", err
	}
	if u.Scheme == "" {
		u.Scheme = "https"
	}
	return u.String(), nil
}
