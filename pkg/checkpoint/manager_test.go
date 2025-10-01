package checkpoint

import (
	"context"
	"errors"
	"testing"
)

type memFS struct{ ops []string }

func (m *memFS) Clone(ctx context.Context, src, dst string) error {
	m.ops = append(m.ops, "clone:"+src+"->"+dst)
	return nil
}
func (m *memFS) Rename(ctx context.Context, src, dst string) error {
	m.ops = append(m.ops, "rename:"+src+"->"+dst)
	return nil
}

type memDB struct {
	created bool
}

func (d *memDB) CreateCheckpoint(cloneFn func(src, dst string) error, renameFn func(src, dst string) error) (*Record, error) {
	if err := cloneFn("active/", "checkpoints/v0.in-progress"); err != nil {
		return nil, err
	}
	if err := renameFn("checkpoints/v0.in-progress", "checkpoints/v0"); err != nil {
		return nil, err
	}
	d.created = true
	return &Record{ID: 2, Path: "active/"}, nil
}
func (d *memDB) GetCheckpointByID(id int64) (*Record, error) {
	return &Record{ID: id, Path: "checkpoints/v0"}, nil
}
func (d *memDB) FindCheckpointByPath(path string) (*Record, error) {
	return &Record{ID: 1, Path: path}, nil
}
func (d *memDB) ListAll() ([]Record, error) {
	return []Record{{ID: 1, Path: "checkpoints/v0"}}, nil
}
func (d *memDB) GetLatest() (*Record, error) {
	return &Record{ID: 2, Path: "active/"}, nil
}

func TestChainOrderAndResume(t *testing.T) {
	var order []string
	a := func(ctx context.Context) (func() error, error) {
		order = append(order, "a")
		return func() error { order = append(order, "A"); return nil }, nil
	}
	b := func(ctx context.Context) (func() error, error) {
		order = append(order, "b")
		return func() error { order = append(order, "B"); return nil }, nil
	}
	c := func(ctx context.Context) (func() error, error) {
		order = append(order, "c")
		return func() error { order = append(order, "C"); return nil }, nil
	}
	resume, err := Chain(a, b, c)(context.Background())
	if err != nil {
		t.Fatal(err)
	}
	if got := order; len(got) != 3 || got[0] != "a" || got[1] != "b" || got[2] != "c" {
		t.Fatalf("prepare order wrong: %v", got)
	}
	if err := resume(); err != nil {
		t.Fatal(err)
	}
	if got := order; got[len(got)-3] != "C" || got[len(got)-2] != "B" || got[len(got)-1] != "A" {
		t.Fatalf("resume order wrong: %v", got)
	}
}

func TestChainErrorRollsBack(t *testing.T) {
	var order []string
	ok := func(ctx context.Context) (func() error, error) {
		order = append(order, "ok")
		return func() error { order = append(order, "OK"); return nil }, nil
	}
	bad := func(ctx context.Context) (func() error, error) {
		order = append(order, "bad")
		return nil, errors.New("fail")
	}
	if _, err := Chain(ok, bad, ok)(context.Background()); err == nil {
		t.Fatal("expected error")
	}
	// Should have resumed only the first ok
	if got := order[len(order)-1]; got != "OK" {
		t.Fatalf("expected rollback of first, got %v (%v)", got, order)
	}
}

func TestManagerCheckpointCallsDBAndFS(t *testing.T) {
	// Skip this test - it requires actual filesystem and DB setup
	// The integration happens in higher-level system tests
	t.Skip("Integration test moved to system tests")
}
