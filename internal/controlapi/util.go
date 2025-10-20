package controlapi

import (
	"crypto/rand"
	"encoding/hex"
)

func newControlID() string {
	var b [8]byte
	if _, err := rand.Read(b[:]); err != nil {
		return "cid-00000000"
	}
	return "cid-" + hex.EncodeToString(b[:])
}
