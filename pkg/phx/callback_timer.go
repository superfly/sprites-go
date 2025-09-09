package phx

import (
	"sync"
	"time"
)

type timerCallback func()

type timerCalculator func(tries int) time.Duration

type callbackTimer struct {
	mu        sync.Mutex
	callback  timerCallback
	timerCalc timerCalculator
	timer     *time.Timer
	tries     int
}

func newCallbackTimer(callback timerCallback, timerCalc timerCalculator) *callbackTimer {
	return &callbackTimer{
		callback:  callback,
		timerCalc: timerCalc,
		timer:     nil,
		tries:     0,
	}
}

func (t *callbackTimer) Reset() {
	t.mu.Lock()
	defer t.mu.Unlock()

	t.tries = 0
	if t.timer != nil {
		t.timer.Stop()
		t.timer = nil
	}
}

func (t *callbackTimer) Run() {
	t.mu.Lock()
	defer t.mu.Unlock()

	if t.timer != nil {
		t.timer.Stop()
		t.timer = nil
	}

	t.timer = time.AfterFunc(t.timerCalc(t.tries+1), func() {
		t.mu.Lock()
		defer t.mu.Unlock()

		t.tries++
		t.callback()
	})
}
