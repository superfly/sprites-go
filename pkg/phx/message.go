package phx

import (
	"encoding/json"
	"strconv"
)

// Message is a message sent or received via the socket after encoding/decoding
type Message struct {
	// JoinRef is the unique Ref sent when a JoinEvent is sent to join a channel. JoinRef can also be though of as
	// a Channel ref. If present, this message is tied to the given instance of a Channel.
	JoinRef Ref

	// Ref is the unique Ref for a given message. When sending a new Message, a Ref should be generated. When a reply
	// is sent back from the server, it will have Ref set to match the Message it is a reply to.
	Ref Ref

	// Topic is the Channel topic this message is in relation to, as defined on the server side.
	Topic string

	// Event is a string description of what this message is about, and can be set to anything the user desires.
	// Some Events are reserved for specific protocol messages as defined in event.go.
	Event string

	// Payload is any arbitrary data attached to the message.
	Payload any
}

func (m Message) MarshalJSON() ([]byte, error) {
	//fmt.Printf("Message.MarshalJSON %+v\n", m)
	jsonMessage := NewJSONMessage(m)
	data, err := json.Marshal(jsonMessage)
	if err != nil {
		return nil, err
	}
	//fmt.Printf("Message.MarshalJSON %+v -> %s\n", m, data)
	return data, nil
}

func (m *Message) UnmarshalJSON(data []byte) error {
	//fmt.Printf("Message.UnMarshalJSON %s\n", data)
	var jm JSONMessage
	err := json.Unmarshal(data, &jm)
	if err != nil {
		return err
	}
	msg, err := jm.Message()
	if err != nil {
		return err
	}
	// make a copy
	*m = *msg
	//fmt.Printf("Message.UnMarshalJSON %s -> %+v\n", data, m)
	return nil
}

// JSONMessage is a JSON representation of a Message
type JSONMessage struct {
	JoinRef string `json:"join_ref,omitempty"`
	Ref     string `json:"ref"`
	Topic   string `json:"topic"`
	Event   string `json:"event"`
	Payload any    `json:"payload"`
}

func NewJSONMessage(msg Message) *JSONMessage {
	jm := &JSONMessage{
		Ref:     strconv.FormatUint(uint64(msg.Ref), 10),
		Topic:   msg.Topic,
		Event:   msg.Event,
		Payload: msg.Payload,
	}
	if msg.JoinRef != 0 {
		jm.JoinRef = strconv.FormatUint(uint64(msg.JoinRef), 10)
	}
	return jm
}

func (jm *JSONMessage) Message() (*Message, error) {
	//fmt.Printf("JSONMessage.Message: %#v\n", jm)
	joinRef, err := ParseRef(jm.JoinRef)
	if err != nil {
		return nil, err
	}

	ref, err := ParseRef(jm.Ref)
	if err != nil {
		return nil, err
	}

	msg := Message{
		JoinRef: joinRef,
		Ref:     ref,
		Topic:   jm.Topic,
		Event:   jm.Event,
		Payload: jm.Payload,
	}

	return &msg, nil
}
