package main

import (
	"context"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"os"
	"strings"

	"github.com/superfly/sprite-env/internal/releaser/clients"
	rctx "github.com/superfly/sprite-env/internal/releaser/context"
	"github.com/superfly/sprite-env/internal/releaser/images"
	"github.com/superfly/sprite-env/internal/releaser/registry"
)

type ghaOutputs struct{}

func (ghaOutputs) write(k, v string) error {
	path := os.Getenv("GITHUB_OUTPUT")
	if path == "" {
		return fmt.Errorf("GITHUB_OUTPUT not set")
	}
	f, err := os.OpenFile(path, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
	if err != nil {
		return err
	}
	defer f.Close()
	if _, err := fmt.Fprintf(f, "%s=%s\n", k, v); err != nil {
		return err
	}
	return nil
}

func cmdContext(args []string) error {
	fs := flag.NewFlagSet("context", flag.ContinueOnError)
	gha := fs.Bool("gha-outputs", false, "Write key=value to $GITHUB_OUTPUT in addition to JSON")
	distro := fs.String("distro", "25.04", "Ubuntu distro prefix for tags")
	if err := fs.Parse(args); err != nil {
		return err
	}
	c, err := rctx.Derive(context.Background())
	if err != nil {
		return err
	}
	out := rctx.RenderContext(*c, *distro)
	enc := json.NewEncoder(os.Stdout)
	enc.SetIndent("", "  ")
	if err := enc.Encode(out); err != nil {
		return err
	}
	if *gha {
		w := ghaOutputs{}
		// Maintain compatibility with existing workflow outputs
		if err := w.write("ubuntu_tag", out.UbuntuTag); err != nil {
			return err
		}
		if err := w.write("sprite_env_tag", out.ServerTag); err != nil {
			return err
		}
		if err := w.write("is_version_tag", fmt.Sprintf("%v", out.IsVersionTag)); err != nil {
			return err
		}
		if err := w.write("previous_tag", out.PreviousTagNoV); err != nil {
			return err
		}
		if err := w.write("short-sha", out.ShortSHA); err != nil {
			return err
		}
		if err := w.write("mode", out.Mode); err != nil {
			return err
		}
		if err := w.write("tag_latest_base", fmt.Sprintf("%v", out.TagLatestBase)); err != nil {
			return err
		}
		if err := w.write("tag_latest_lang", fmt.Sprintf("%v", out.TagLatestLang)); err != nil {
			return err
		}
		if err := w.write("tag_latest_server", fmt.Sprintf("%v", out.TagLatestServer)); err != nil {
			return err
		}
		if err := w.write("client_upload_prefix", out.ClientUploadPrefix); err != nil {
			return err
		}
		if err := w.write("client_channel_file", out.ClientChannelFile); err != nil {
			return err
		}
		if err := w.write("client_channel_value", out.ClientChannelValue); err != nil {
			return err
		}
		if out.Mode == "dev" {
			if err := w.write("dev_version", out.DevVersion); err != nil {
				return err
			}
		}
	}
	return nil
}

func cmdImages(args []string) error {
	if len(args) == 0 {
		return errors.New("images subcommand required: plan|retag")
	}
	switch args[0] {
	case "plan":
		fs := flag.NewFlagSet("images plan", flag.ContinueOnError)
		registryHost := fs.String("registry", "ghcr.io", "OCI registry host")
		ubuntuImage := fs.String("ubuntu-image", "superfly/sprite-ubuntu", "Repository name for Ubuntu images (no registry host)")
		distro := fs.String("distro", "25.04", "Ubuntu distro prefix for tags")
		gha := fs.Bool("gha-outputs", false, "Write plan to $GITHUB_OUTPUT as well as JSON")
		if err := fs.Parse(args[1:]); err != nil {
			return err
		}
		ctx, err := rctx.Derive(context.Background())
		if err != nil {
			return err
		}
		rc := rctx.RenderContext(*ctx, *distro)
		reg := registry.New(*registryHost)
		plan, err := images.Plan(context.Background(), reg, rc, *ubuntuImage)
		if err != nil {
			return err
		}
		enc := json.NewEncoder(os.Stdout)
		enc.SetIndent("", "  ")
		if err := enc.Encode(plan); err != nil {
			return err
		}
		if *gha {
			w := ghaOutputs{}
			if err := w.write("base_action", string(plan.Base.Action)); err != nil {
				return err
			}
			if err := w.write("base_source_tag", plan.Base.SourceTag); err != nil {
				return err
			}
			if err := w.write("base_target_tag", plan.Base.TargetTag); err != nil {
				return err
			}
			if err := w.write("base_latest_tag", plan.Base.LatestTag); err != nil {
				return err
			}
			if err := w.write("languages_action", string(plan.Languages.Action)); err != nil {
				return err
			}
			if err := w.write("languages_source_tag", plan.Languages.SourceTag); err != nil {
				return err
			}
			if err := w.write("languages_target_tag", plan.Languages.TargetTag); err != nil {
				return err
			}
			if err := w.write("languages_latest_tag", plan.Languages.LatestTag); err != nil {
				return err
			}
			if err := w.write("server_tag", plan.ServerTag); err != nil {
				return err
			}
		}
		return nil

	case "retag":
		fs := flag.NewFlagSet("images retag", flag.ContinueOnError)
		image := fs.String("image", "ghcr.io/superfly/sprite-ubuntu", "Fully-qualified image repo, including registry")
		source := fs.String("source", "", "Source tag to copy from")
		target := fs.String("target", "", "Target tag to create")
		alsoLatest := fs.String("also-latest", "", "Optional 'latest' tag to also write")
		if err := fs.Parse(args[1:]); err != nil {
			return err
		}
		if *source == "" || *target == "" {
			return errors.New("--source and --target are required")
		}
		reg := registry.NewFromFQRepo(*image)
		if err := reg.CopyTag(context.Background(), *source, *target); err != nil {
			return err
		}
		if strings.TrimSpace(*alsoLatest) != "" {
			if err := reg.CopyTag(context.Background(), *target, *alsoLatest); err != nil {
				return err
			}
		}
		fmt.Println("retagged")
		return nil
	default:
		return fmt.Errorf("unknown images subcommand: %s", args[0])
	}
}

func cmdClients(args []string) error {
	sub := ""
	if len(args) > 0 {
		sub = args[0]
	}
	switch sub {
	case "publish":
		fs := flag.NewFlagSet("clients publish", flag.ContinueOnError)
		artifacts := fs.String("artifacts-dir", "artifacts", "Directory containing built client artifacts")
		bucket := fs.String("bucket", "sprites-binaries", "S3 bucket name")
		endpoint := fs.String("endpoint", "", "S3-compatible endpoint URL")
		mode := fs.String("mode", "dev", "Mode: dev or prod")
		version := fs.String("version", "", "Version tag (vX.Y.Z for prod; X.Y.Z-dev-<sha> for dev)")
		dryRun := fs.Bool("dry-run", false, "Do not upload; print actions")
		if err := fs.Parse(args[1:]); err != nil {
			return err
		}
		m := clients.Mode(*mode)
		return clients.Publish(context.Background(), clients.PublishOptions{
			ArtifactsDir: *artifacts,
			Bucket:       *bucket,
			Endpoint:     *endpoint,
			Mode:         m,
			Version:      *version,
			DryRun:       *dryRun,
		})
	default:
		return fmt.Errorf("unknown clients subcommand: %s", sub)
	}
}

func main() {
	if len(os.Args) < 2 {
		fmt.Fprintln(os.Stderr, "usage: releaser <context|images>")
		os.Exit(2)
	}
	var err error
	switch os.Args[1] {
	case "context":
		err = cmdContext(os.Args[2:])
	case "images":
		err = cmdImages(os.Args[2:])
	case "clients":
		err = cmdClients(os.Args[2:])
	default:
		err = fmt.Errorf("unknown command: %s", os.Args[1])
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, "error:", err)
		os.Exit(1)
	}
}
