package clients

import (
	"context"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"

	"github.com/aws/aws-sdk-go-v2/aws"
	"github.com/aws/aws-sdk-go-v2/config"
	"github.com/aws/aws-sdk-go-v2/service/s3"
)

type Mode string

const (
	ModeProd Mode = "prod"
	ModeDev  Mode = "dev"
)

type PublishOptions struct {
	ArtifactsDir string
	Bucket       string
	Endpoint     string // S3-compatible endpoint
	Mode         Mode
	Version      string // vX.Y.Z for prod; X.Y.Z-dev-<sha> for dev
	DryRun       bool
}

func hashFile(path string) (string, error) {
	f, err := os.Open(path)
	if err != nil {
		return "", err
	}
	defer f.Close()
	h := sha256.New()
	if _, err := io.Copy(h, f); err != nil {
		return "", err
	}
	return hex.EncodeToString(h.Sum(nil)), nil
}

func ensureChecksum(path string) (string, error) {
	sum, err := hashFile(path)
	if err != nil {
		return "", err
	}
	sumPath := path + ".sha256"
	if err := os.WriteFile(sumPath, []byte(fmt.Sprintf("%s  %s\n", sum, filepath.Base(path))), 0644); err != nil {
		return "", err
	}
	return sumPath, nil
}

func s3Client(ctx context.Context, endpoint string) (*s3.Client, error) {
	// Use env credentials; allow endpoint override
	cfg, err := config.LoadDefaultConfig(ctx)
	if err != nil {
		return nil, err
	}
	client := s3.NewFromConfig(cfg, func(o *s3.Options) {
		if strings.TrimSpace(endpoint) != "" {
			o.BaseEndpoint = aws.String(endpoint)
		}
		o.UsePathStyle = true
	})
	return client, nil
}

func putObject(ctx context.Context, s3c *s3.Client, bucket, key, path string) error {
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	_, err = s3c.PutObject(ctx, &s3.PutObjectInput{Bucket: &bucket, Key: &key, Body: f})
	return err
}

// Publish uploads client artifacts and channel files.
func Publish(ctx context.Context, opt PublishOptions) error {
	// Discover files
	var files []string
	err := filepath.WalkDir(opt.ArtifactsDir, func(path string, d os.DirEntry, err error) error {
		if err != nil {
			return err
		}
		if d.IsDir() {
			return nil
		}
		if strings.HasSuffix(path, ".tar.gz") || strings.HasSuffix(path, ".zip") {
			files = append(files, path)
		}
		return nil
	})
	if err != nil {
		return err
	}
	// Generate checksums
	var toUpload []string
	for _, f := range files {
		toUpload = append(toUpload, f)
		sum, err := ensureChecksum(f)
		if err != nil {
			return err
		}
		toUpload = append(toUpload, sum)
	}

	// Keys
	var prefix string
	var channelFile string
	var channelContent string
	switch opt.Mode {
	case ModeProd:
		if !strings.HasPrefix(opt.Version, "v") {
			return fmt.Errorf("prod mode requires version starting with v, got %q", opt.Version)
		}
		prefix = fmt.Sprintf("client/%s/", opt.Version)
		channelFile = "client/release.txt"
		channelContent = opt.Version
	case ModeDev:
		prefix = "client/dev-latest/"
		channelFile = "client/dev.txt"
		channelContent = opt.Version
	default:
		return fmt.Errorf("unknown mode: %s", opt.Mode)
	}

	if opt.DryRun {
		for _, f := range toUpload {
			fmt.Printf("DRY-RUN put s3://%s/%s%s\n", opt.Bucket, prefix, filepath.Base(f))
		}
		fmt.Printf("DRY-RUN put s3://%s/%s\n", opt.Bucket, channelFile)
		return nil
	}

	s3c, err := s3Client(ctx, opt.Endpoint)
	if err != nil {
		return err
	}
	for _, f := range toUpload {
		key := prefix + filepath.Base(f)
		if err := putObject(ctx, s3c, opt.Bucket, key, f); err != nil {
			return err
		}
	}
	tmp, err := os.CreateTemp("", "channel-*.txt")
	if err != nil {
		return err
	}
	if _, err := tmp.WriteString(channelContent); err != nil {
		return err
	}
	if err := tmp.Close(); err != nil {
		return err
	}
	if err := putObject(ctx, s3c, opt.Bucket, channelFile, tmp.Name()); err != nil {
		return err
	}
	return nil
}
