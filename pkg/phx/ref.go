package phx

import (
	"fmt"
	"strconv"
	"sync/atomic"
)

// Ref is a unique reference integer that is atomically incremented and will wrap at 64 bits + 1
type Ref uint64

func ParseRef(ref any) (Ref, error) {
	if ref == nil {
		return Ref(0), nil
	}
	switch v := ref.(type) {
	case string:
		if ref == "" {
			return 0, nil
		}
		refUint, err := strconv.ParseUint(v, 10, 64)
		if err != nil {
			return 0, err
		}
		return Ref(refUint), nil
	case uint64:
		return Ref(v), nil
	}
	return 0, fmt.Errorf("cannot convert %#v to Ref", ref)
}

type atomicRef struct {
	ref *uint64
}

func newAtomicRef() *atomicRef {
	return &atomicRef{
		ref: new(uint64),
	}
}

func (ic *atomicRef) nextRef() Ref {
	return Ref(atomic.AddUint64(ic.ref, 1))
}
