package sprites

import (
	"net/http"

	clientsignals "github.com/superfly/client-signals/go"
)

// WithClientSignals attaches coarse, privacy-safe client-signal headers
// (interactive/CI/agent detection; see github.com/superfly/client-signals)
// to every outgoing request the Client makes — both plain HTTP calls and
// the WebSocket dials used for exec/proxy/control connections. Pass the
// result of clientsignals.DetectOnce() (or Detect()), computed once by the
// caller.
//
// Disabled by default; a nil sig is a no-op.
func WithClientSignals(sig *clientsignals.Signals) Option {
	return func(c *Client) {
		c.clientSignals = sig
	}
}

// applyClientSignalHeaders sets the same Fly-Client-* headers that
// clientsignals.Signals.WrapTransport applies to plain HTTP requests, for
// use on WebSocket dials that bypass the Client's http.Client entirely. A
// nil sig is a no-op.
func applyClientSignalHeaders(header http.Header, sig *clientsignals.Signals) {
	if sig == nil {
		return
	}
	sig.ApplyHeaders(header)
}
