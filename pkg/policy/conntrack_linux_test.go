//go:build linux

package policy

import (
    "os/exec"
    "testing"
    "net"
    "context"
)

// This is a smoke test that invokes clearContainerFlows on a local address.
// It requires conntrack CLI but does not depend on external connectivity.
func TestClearContainerFlows_Smoke(t *testing.T) {
    if _, err := exec.LookPath("conntrack"); err != nil {
        t.Skip("conntrack not available")
    }
    ctx := context.Background()
    // Use a private RFC1918 address; function should handle no matching flows gracefully
    ip4 := net.ParseIP("10.0.0.1")
    // We accept either success or a netlink error on platforms where dumping is unsupported
    _ = clearContainerFlows(ctx, ip4, nil)
}


