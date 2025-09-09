package phx

import (
	"fmt"
	"sync"
	"time"
)

type channelBinding struct {
	ref      Ref
	event    string
	callback func(payload any)
}

// A Channel is a unique connection to the given Topic on the server. You can have many Channels connected over one
// Socket, each handling messages independently.
type Channel struct {
	// PushTimeout is the time that a Push waits before considering it defunct and triggering a "timeout" event.
	PushTimeout time.Duration

	// RejoinAfterFunc is a function that returns the duration to wait before rejoining based on given tries
	RejoinAfterFunc func(tries int) time.Duration

	// private
	topic           string
	params          map[string]string
	mu              sync.RWMutex
	socket          *Socket
	state           ChannelState
	refGenerator    *atomicRef
	joinPush        *Push
	bindings        map[Ref]*channelBinding
	rejoinTimer     *callbackTimer
	socketCallbacks []Ref
}

// NewChannel creates a new Channel attached to the Socket. If there is already a Channel for the given topic, that
// channel is returned instead of creating a new one.
func NewChannel(topic string, params map[string]string, socket *Socket) *Channel {
	channel, exists := socket.getChannel(topic)
	if exists {
		return channel
	}

	c := &Channel{
		PushTimeout:     defaultPushTimeout,
		RejoinAfterFunc: defaultRejoinAfterFunc,
		topic:           topic,
		params:          params,
		socket:          socket,
		state:           ChannelClosed,
		refGenerator:    newAtomicRef(),
		bindings:        make(map[Ref]*channelBinding),
		socketCallbacks: make([]Ref, 0, 2),
	}

	c.rejoinTimer = newCallbackTimer(c.rejoin, c.RejoinAfterFunc)

	c.OnClose(func(payload any) {
		c.socket.Logger.Printf(LogInfo, "channel", "Channel '%v' closed. joinRef: %v", c.topic, c.JoinRef())
		c.setState(ChannelClosed)
		c.rejoinTimer.Reset()
	})

	c.OnError(func(payload any) {
		c.socket.Logger.Printf(LogError, "channel", "Channel '%v' error: %+v", c.topic, payload)
		c.setState(ChannelErrored)
		c.rejoinTimer.Run()
	})

	c.socketCallbacks = append(c.socketCallbacks, socket.OnOpen(func() {
		c.rejoinTimer.Reset()
		if c.IsErrored() {
			c.rejoin()
		}
	}))
	c.socketCallbacks = append(c.socketCallbacks, socket.OnClose(func() {
		c.rejoinTimer.Reset()
		if c.IsJoined() || c.IsJoining() {
			c.setState(ChannelErrored)
			c.trigger(string(ErrorEvent), 0, nil)
		}
	}))
	c.socketCallbacks = append(c.socketCallbacks, socket.OnError(func(err error) {
		c.setState(ChannelErrored)
		c.trigger(string(ErrorEvent), 0, nil)
		c.rejoinTimer.Reset()
	}))

	// Add this channel to the socket's open channel
	socket.addChannel(c)

	return c
}

// Join will send a JoinEvent to the server and attempt to join the topic of this Channel.
// A Push is returned to which you can attach event handlers to with Receive, such as "ok", "error" and "timeout".
func (c *Channel) Join() (*Push, error) {
	if c.IsRemoved() {
		return nil, fmt.Errorf("channel removed, create a new Channel")
	}
	if c.IsJoined() {
		return nil, fmt.Errorf("already joined")
	}
	if c.IsJoining() {
		return nil, fmt.Errorf("join already in progress")
	}
	if !c.socket.IsConnectedOrConnecting() {
		return nil, fmt.Errorf("cannot join before connecting the socket")
	}

	joinPush := NewPush(c, string(JoinEvent), c.params, c.PushTimeout)
	c.setJoinPush(joinPush)
	joinPush.Receive("ok", func(response any) {
		c.socket.Logger.Printf(LogInfo, "channel", "joined channel '%v' joinRef:%v", c.topic, c.JoinRef())
		c.setState(ChannelJoined)
		c.trigger(string(JoinEvent), 0, response)
		c.rejoinTimer.Reset()
	})
	joinPush.Receive("error", func(response any) {
		c.socket.Logger.Printf(LogError, "channel", "error joining channel '%v': %v", c.topic, response)
		c.setState(ChannelErrored)
		joinPush.reset()
		c.rejoinTimer.Run()
	})
	joinPush.Receive("timeout", func(response any) {
		c.socket.Logger.Printf(LogError, "channel", "timeout joining channel '%v'", c.topic)
		joinPush.reset()

		// Fire-and-forget a leave push
		leavePush := NewPush(c, string(LeaveEvent), c.params, c.PushTimeout)
		_ = leavePush.Send()

		c.setState(ChannelErrored)
		c.rejoinTimer.Run()
	})

	c.setState(ChannelJoining)
	err := joinPush.Send()
	if err != nil {
		return nil, err
	}

	return joinPush, nil
}

// Leave will send a LeaveEvent to the server to leave the topic of this Channel
// A Push is returned to which you can attach event handlers to with Receive, such as "ok", "error" and "timeout".
func (c *Channel) Leave() (*Push, error) {
	if c.IsRemoved() {
		return nil, fmt.Errorf("channel removed, create a new Channel")
	}
	if c.IsClosed() {
		return nil, fmt.Errorf("cannot leave closed channel")
	}
	if c.IsLeaving() {
		return nil, fmt.Errorf("leave already in progress")
	}

	c.rejoinTimer.Reset()
	c.setState(ChannelLeaving)

	// Send a leave message even if we aren't connected and joined
	leavePush := NewPush(c, string(LeaveEvent), c.params, c.PushTimeout)
	leavePush.Receive("ok", func(response any) {
		c.socket.Logger.Printf(LogInfo, "channel", "left channel '%v'", c.topic)
		c.trigger(string(CloseEvent), 0, "leave")
	})
	leavePush.Receive("error", func(response any) {
		c.socket.Logger.Printf(LogError, "channel", "error leaving channel '%v': %v", c.topic, response)
		c.trigger(string(CloseEvent), 0, "leave")
	})
	leavePush.Receive("timeout", func(response any) {
		c.socket.Logger.Printf(LogError, "channel", "timeout leaving channel '%v'", c.topic)
	})

	if c.socket.IsConnected() {
		err := leavePush.Send()
		if err != nil {
			return nil, err
		}
	} else {
		// If we're not connected, there is no channel on the server to leave, so just mark us left
		c.setState(ChannelClosed)
		leavePush.trigger("ok", "leave")
	}

	return leavePush, nil
}

// Remove will remove this channel from the Socket. Once this is done, the channel will no longer receive any kind of
// messages, and be essentially orphaned, so it is important that you also remove all references to the Channel so that
// it can be garbage collected.
func (c *Channel) Remove() error {
	if c.IsJoined() || c.IsJoining() {
		return fmt.Errorf("must Leave channel before removing")
	}
	c.setState(ChannelRemoved)
	c.socket.removeChannel(c)
	for _, ref := range c.socketCallbacks {
		c.socket.Off(ref)
	}
	return nil
}

// Push will send the given Event and Payload to the server. A Push is returned to which you can attach event handlers
// to with Receive() so you can process replies.
func (c *Channel) Push(event string, payload any) (*Push, error) {
	if c.IsRemoved() {
		return nil, fmt.Errorf("channel removed, create a new Channel")
	}
	if c.joinPush == nil {
		return nil, fmt.Errorf("cannot push before calling Join")
	}

	push := NewPush(c, event, payload, c.PushTimeout)
	err := push.Send()
	return push, err
}

// On will register the given callback for all matching events received on this Channel.
// Returns a unique Ref that can be used to cancel this callback via Off.
func (c *Channel) On(event string, callback func(payload any)) (bindingRef Ref) {
	bindingRef = c.refGenerator.nextRef()

	c.mu.Lock()
	defer c.mu.Unlock()

	c.bindings[bindingRef] = &channelBinding{
		event:    event,
		callback: callback,
	}
	return
}

// OnRef will register the given callback for all matching events only if the ref also matches.
// This is mostly used by Push so that it can get ReplyEvents for its messages.
// Returns a unique Ref that can be used to cancel this callback via Off.
func (c *Channel) OnRef(ref Ref, event string, callback func(payload any)) (bindingRef Ref) {
	bindingRef = c.refGenerator.nextRef()

	c.mu.Lock()
	defer c.mu.Unlock()

	c.bindings[bindingRef] = &channelBinding{
		ref:      ref,
		event:    event,
		callback: callback,
	}
	return
}

// OnJoin will register the given callback for whenever this Channel joins successfully to the server.
// Returns a unique Ref that can be used to cancel this callback via Off.
func (c *Channel) OnJoin(callback func(payload any)) (bindingRef Ref) {
	return c.On(string(JoinEvent), callback)
}

// OnClose will register the given callback for whenever this Channel is closed.
// Returns a unique Ref that can be used to cancel this callback via Off.
func (c *Channel) OnClose(callback func(payload any)) (bindingRef Ref) {
	return c.On(string(CloseEvent), callback)
}

// OnError will register the given callback for whenever this channel gets an ErrorEvent message, such as the channel
// process crashing.
// Returns a unique Ref that can be used to cancel this callback via Off.
func (c *Channel) OnError(callback func(payload any)) (bindingRef Ref) {
	return c.On(string(ErrorEvent), callback)
}

// Off removes the callback for the given bindingRef, as returned by On, OnRef, OnJoin, OnClose, OnError.
func (c *Channel) Off(bindingRef Ref) {
	c.mu.Lock()
	defer c.mu.Unlock()

	delete(c.bindings, bindingRef)
}

// Clear removes all bindings for the given event
func (c *Channel) Clear(event string) {
	c.mu.Lock()
	defer c.mu.Unlock()

	for ref, binding := range c.bindings {
		if binding.event == event {
			delete(c.bindings, ref)
		}
	}
}

// rejoin is a callback for the rejoinTimer, and shouldn't be called directly. It runs in a separate goroutine.
func (c *Channel) rejoin() {
	if c.IsRemoved() || c.IsJoined() || c.IsJoining() || c.IsLeaving() {
		return
	}

	if !c.socket.IsConnected() {
		return
	}

	push := c.getJoinPush()
	if push == nil {
		c.socket.Logger.Println(LogWarning, "channel", "rejoin called before joinPush created!")
		return
	}

	c.socket.Logger.Println(LogInfo, "channel", "attempting to rejoin channel")
	err := push.Send()
	if err != nil {
		c.socket.Logger.Println(LogError, "channel", "error on rejoin push", err)
	}
}

// process messages received from Socket
func (c *Channel) process(msg *Message) {
	if c.IsRemoved() {
		// this shouldn't happen, but just in case
		return
	}

	// We only care about messages that match our topic
	if msg.Topic != c.topic {
		return
	}

	// Replies will have a joinRef set to the Ref we joined with. If it doesn't match, then it's an old message
	// from a previous join, and we should discard it.
	if msg.JoinRef != 0 && msg.JoinRef != c.JoinRef() {
		c.socket.Logger.Println(LogWarning, "channel", "dropping stale message", msg)
		return
	}

	// Trigger bindings with this event
	c.trigger(msg.Event, msg.Ref, msg.Payload)
}

// trigger calls all bindings (callbacks) that are interested in this event. For bindings that have also given us a
// ref, only call the callback if the ref matches. This is so that Push can process ReplyEvents that only match its
// ref, thus are a reply to that specific Push.
func (c *Channel) trigger(event string, ref Ref, payload any) {
	c.mu.RLock()
	defer c.mu.RUnlock()

	// For a given channelBinding to get called it must match the event and either have ref == 0 or match the ref
	for _, binding := range c.bindings {
		if binding.event == event && (binding.ref == 0 || binding.ref == ref) {
			go binding.callback(payload)
		}
	}
}

func (c *Channel) setJoinPush(push *Push) {
	c.mu.Lock()
	defer c.mu.Unlock()

	c.joinPush = push
}

func (c *Channel) getJoinPush() *Push {
	c.mu.RLock()
	defer c.mu.RUnlock()

	return c.joinPush
}

// Topic returns the topic for this channel
func (c *Channel) Topic() string {
	return c.topic
}

// JoinRef returns the JoinRef for this channel, which is the Ref of the Push returned by Join
func (c *Channel) JoinRef() Ref {
	c.mu.RLock()
	defer c.mu.RUnlock()

	if c.joinPush != nil {
		return c.joinPush.Ref
	} else {
		return 0
	}
}

func (c *Channel) setState(state ChannelState) {
	c.mu.Lock()
	defer c.mu.Unlock()

	c.state = state
}

// State returns the current ChannelState of this channel. Can also use Is*() functions
func (c *Channel) State() ChannelState {
	c.mu.RLock()
	defer c.mu.RUnlock()

	return c.state
}

func (c *Channel) IsClosed() bool {
	c.mu.RLock()
	defer c.mu.RUnlock()

	return c.state == ChannelClosed
}

func (c *Channel) IsErrored() bool {
	c.mu.RLock()
	defer c.mu.RUnlock()

	return c.state == ChannelErrored
}

func (c *Channel) IsJoined() bool {
	c.mu.RLock()
	defer c.mu.RUnlock()

	return c.state == ChannelJoined
}

func (c *Channel) IsJoining() bool {
	c.mu.RLock()
	defer c.mu.RUnlock()

	return c.state == ChannelJoining
}

func (c *Channel) IsLeaving() bool {
	c.mu.RLock()
	defer c.mu.RUnlock()

	return c.state == ChannelLeaving
}

func (c *Channel) IsRemoved() bool {
	c.mu.RLock()
	defer c.mu.RUnlock()

	return c.state == ChannelRemoved
}
