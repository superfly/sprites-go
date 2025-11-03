package images

import (
	"context"
	"fmt"
	"os"
	"strings"

	rctx "github.com/superfly/sprite-env/internal/releaser/context"
	"github.com/superfly/sprite-env/internal/releaser/registry"
)

type Action string

const (
	ActionBuild Action = "build"
	ActionRetag Action = "retag"
)

type ImagePlan struct {
	Action    Action `json:"action"`
	SourceTag string `json:"sourceTag,omitempty"`
	TargetTag string `json:"targetTag"`
	LatestTag string `json:"latestTag,omitempty"`
}

type PlanOutput struct {
	Base      ImagePlan `json:"base"`
	Languages ImagePlan `json:"languages"`
	ServerTag string    `json:"serverTag"`
}

// Plan decides whether to build or retag ubuntu base and languages images.
// It mirrors the current YAML logic, simplified and made explicit.
func Plan(ctx context.Context, reg *registry.Client, rc rctx.Output, ubuntuRepo string) (*PlanOutput, error) {
	p := &PlanOutput{ServerTag: rc.ServerTag}

	// Determine latest tag names (only if context has them enabled)
	latestBase := ""
	latestLang := ""
	if rc.TagLatestBase {
		latestBase = "25.04-latest"
	}
	if rc.TagLatestLang {
		latestLang = "25.04-languages-latest"
	}

	// Evaluate base image
	baseTarget := rc.UbuntuTag
	base := ImagePlan{TargetTag: baseTarget, LatestTag: latestBase}

	var sourceBase string
	prev := strings.TrimSpace(rc.PreviousTagNoV)
	if prev != "" {
		// Only retag from previous when there are no changes in the image build context
		since := os.Getenv("RELEASER_DIFF_SINCE")
		until := os.Getenv("RELEASER_DIFF_UNTIL")
		if strings.TrimSpace(since) == "" {
			since = "v" + prev
		}
		if strings.TrimSpace(until) == "" {
			until = "HEAD"
		}
		changed, _ := rctx.DiffPathsSince(since, until, []string{"base-env/images/ubuntu-devtools/"})
		if !changed {
			prevTag := fmt.Sprintf("25.04-%s", prev)
			exists, _ := reg.ImageExists(ctx, ubuntuRepo, prevTag)
			if exists {
				sourceBase = prevTag
			}
		}
	}

	// If target already exists in registry, prefer retag from target to allow replacement.
	// For dev tags we also prefer to retag most of the time.
	targetExists, _ := reg.ImageExists(ctx, ubuntuRepo, baseTarget)
	switch {
	case targetExists:
		base.Action = ActionRetag
		base.SourceTag = baseTarget
	case sourceBase != "":
		base.Action = ActionRetag
		base.SourceTag = sourceBase
	default:
		base.Action = ActionBuild
	}
	p.Base = base

	// Languages image mirrors base target with -languages suffix
	langTarget := rc.UbuntuLanguagesTag
	lang := ImagePlan{TargetTag: langTarget, LatestTag: latestLang}

	sourceLang := ""
	if sourceBase != "" {
		sourceLang = sourceBase + "-languages"
	}
	targetLangExists, _ := reg.ImageExists(ctx, ubuntuRepo, langTarget)
	switch {
	case targetLangExists:
		lang.Action = ActionRetag
		lang.SourceTag = langTarget
	case sourceLang != "":
		// Only retag if the source languages image exists
		exists, _ := reg.ImageExists(ctx, ubuntuRepo, sourceLang)
		if exists {
			lang.Action = ActionRetag
			lang.SourceTag = sourceLang
		} else {
			lang.Action = ActionBuild
		}
	default:
		lang.Action = ActionBuild
	}
	p.Languages = lang

	return p, nil
}
