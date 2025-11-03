//go:build linux

package policy

import (
	"context"
	"fmt"
	"net"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/superfly/sprite-env/pkg/tap"
)

// clearContainerFlows flushes the conntrack table by temporarily setting all timeouts to 1 second.
// Our kernels don't have nf_conntrack_netlink so we are just setting a very low ttl as a workaround
// to kill existing conntrack entries.
func clearContainerFlows(ctx context.Context, ipv4, ipv6 net.IP) error {
	logger := tap.Logger(ctx).With("component", "policy", "proc", "conntrack-flush")

	// Save original timeout values
	timeoutFiles := make(map[string]string)
	pattern := "/proc/sys/net/netfilter/nf_conntrack_*timeout*"
	matches, err := filepath.Glob(pattern)
	if err != nil {
		logger.Warn("failed to glob timeout files", "error", err)
		return fmt.Errorf("glob timeout files: %w", err)
	}

	logger.Debug("saving conntrack timeout values", "count", len(matches))

	// Read and save original values
	for _, path := range matches {
		data, err := os.ReadFile(path)
		if err != nil {
			logger.Warn("failed to read timeout file", "path", path, "error", err)
			continue
		}
		timeoutFiles[path] = strings.TrimSpace(string(data))
	}

	// Set all timeouts to 1 second to expire existing connections
	logger.Debug("setting all conntrack timeouts to 1 second")
	for path := range timeoutFiles {
		if err := os.WriteFile(path, []byte("1\n"), 0644); err != nil {
			logger.Warn("failed to set timeout", "path", path, "error", err)
		}
	}

	// Wait for connections to expire
	logger.Debug("waiting for conntrack entries to expire")
	time.Sleep(2 * time.Second)

	// Restore original timeout values
	logger.Debug("restoring original conntrack timeout values", "count", len(timeoutFiles))
	for path, originalValue := range timeoutFiles {
		if err := os.WriteFile(path, []byte(originalValue+"\n"), 0644); err != nil {
			logger.Warn("failed to restore timeout", "path", path, "value", originalValue, "error", err)
		}
	}

	logger.Debug("conntrack flush complete")
	return nil
}


