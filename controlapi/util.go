// Package controlapi (UNSTABLE) provides low-level access to the control websocket.
// This package is intended for advanced users and is subject to change.
package controlapi

import (
	"crypto/rand"
	"encoding/hex"
)

func newControlID() string {
	var b [16]byte
	_, _ = rand.Read(b[:])
	return hex.EncodeToString(b[:])
}
