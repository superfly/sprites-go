package phx

import (
	"sync"
	"time"
)

type pushCallback func(response any)

type pushBinding struct {
	status   string
	callback pushCallback
}

// Push allows you to send an Event to the server and easily monitor for replies, errors or timeouts.
// A Push is typically created by Channel.Join, Channel.Leave and Channel.Push.
type Push struct {
	// Event is the string event you want to push to the server.
	Event string

	// Payload is whatever payload you want to attach to the push. Must be JSON serializable.
	Payload any

	// Timeout is the time to wait for a reply before triggering a "timeout" event.
	Timeout time.Duration

	mu           sync.RWMutex
	channel      *Channel
	Ref          Ref
	timeoutTimer *time.Timer
	callbacks    []*pushBinding
	sent         bool
	bindingRef   Ref
	reply        any
}

// NewPush gets a new Push ready to send and allows you to attach event handlers for replies, errors, timeouts.
func NewPush(channel *Channel, event string, payload any, timeout time.Duration) *Push {
	return &Push{
		channel:   channel,
		Event:     event,
		Payload:   payload,
		Timeout:   timeout,
		Ref:       0,
		callbacks: make([]*pushBinding, 0, 3),
	}
}

// Send will actually push the event to the server.
func (p *Push) Send() error {
	p.reset()
	p.Ref = p.channel.socket.MakeRef()
	p.timeoutTimer = time.AfterFunc(p.Timeout, p.timeout)

	err := p.channel.socket.PushMessage(Message{
		Topic:   p.channel.topic,
		Event:   p.Event,
		Payload: p.Payload,
		Ref:     p.Ref,
		JoinRef: p.channel.JoinRef(),
	})
	if err != nil {
		return err
	}
	p.sent = true

	p.bindingRef = p.channel.OnRef(p.Ref, string(ReplyEvent), func(payload any) {
		// This runs in the Transports goroutine
		p.mu.Lock()
		defer p.mu.Unlock()

		p.cancelTimeout()
		p.channel.Off(p.bindingRef)
		p.reply = payload
		p.callCallbacks(payload)
	})

	return nil
}

func (p *Push) IsSent() bool {
	return p.sent
}

// Receive registers the given event handler for the given status.
// Built in Events such as Join, Leave will respond with "ok", "error" and "timeout".
// Custom event handlers (handle_in/3) in your Channel on the server can respond with any string event they want.
// If a custom event handler (handle_in/3) does not reply (returns :noreply) then the only events that will trigger
// here are "error" and "timeout".
func (p *Push) Receive(status string, callback pushCallback) {
	if p.reply != nil {
		replyStatus, replyResponse, ok := p.deconstructPayload(p.reply)
		if ok && replyStatus == status {
			callback(replyResponse)
			return
		}
	}

	p.mu.Lock()
	defer p.mu.Unlock()
	p.callbacks = append(p.callbacks, &pushBinding{status: status, callback: callback})
}

func (p *Push) callCallbacks(payload any) {
	status, response, ok := p.deconstructPayload(payload)
	if ok {
		p.trigger(status, response)
	}
}

func (p *Push) deconstructPayload(payload any) (status string, response any, ok bool) {
	m, ok := payload.(map[string]any)
	if !ok {
		return
	}
	statusRaw, ok := m["status"]
	if !ok {
		return
	}
	status, ok = statusRaw.(string)
	if !ok {
		return
	}
	response, ok = m["response"]
	if !ok {
		return
	}

	return
}

func (p *Push) trigger(status string, response any) {
	for _, callback := range p.callbacks {
		if callback.status == status {
			go callback.callback(response)
		}
	}
}

func (p *Push) cancelTimeout() {
	if p.timeoutTimer != nil {
		p.timeoutTimer.Stop()
		p.timeoutTimer = nil
	}
}

func (p *Push) timeout() {
	// This runs in the Timer's goroutine
	p.mu.Lock()
	defer p.mu.Unlock()

	p.trigger("timeout", nil)
}

// reset this push so that it will no longer timeout and won't process messages from the server.
func (p *Push) reset() {
	p.cancelTimeout()
	if p.bindingRef != 0 {
		p.channel.Off(p.bindingRef)
	}
	p.Ref = 0
}
