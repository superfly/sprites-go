package runner

import (
	"bytes"
	"os/exec"
	"runtime"
	"sync"
	"testing"
)

func TestConcurrency_Heavy_NoLimit_GOMAXPROCS1(t *testing.T) {
	old := runtime.GOMAXPROCS(1)
	defer runtime.GOMAXPROCS(old)

	r := &Runner{}
	const N = 400
	var wg sync.WaitGroup
	wg.Add(N)
	errs := make(chan error, N)

	for i := 0; i < N; i++ {
		go func() {
			defer wg.Done()
			cmd := exec.Command("sh", "-c", "echo x; echo y 1>&2")
			var out, errb bytes.Buffer
			code, err := r.Run(cmd, WithStdout(&out), WithStderr(&errb))
			if err != nil || code != 0 {
				errs <- err
				return
			}
		}()
	}
	wg.Wait()
	close(errs)
	for e := range errs {
		if e != nil {
			t.Fatalf("error: %v", e)
		}
	}
}
