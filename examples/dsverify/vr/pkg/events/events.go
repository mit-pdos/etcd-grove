package events

import (
	"encoding/json"
	"errors"
	"io"
	"sync"

	"github.com/tangledbytes/go-vsr/pkg/ipv4port"
	"github.com/tangledbytes/go-vsr/pkg/log"
)

type EventType uint8

const (
	EventRequest EventType = iota + 1
	EventReply
	EventPrepare
	EventPrepareOK
	EventCommit
	EventStartViewChange
	EventDoViewChange
	EventStartView
	EventGetState
	EventNewState
	EventHeartbeat
)

// ErrInvalidEventType is returned when an invalid event type is encountered.
var ErrInvalidEventType = errors.New("invalid event type")

type NetworkEvent struct {
	Src   ipv4port.IPv4Port
	Event *Event
}

type Event struct {
	Type EventType `json:"@type"`
	Data any       `json:"data"`
}

type Request struct {
	ID       uint64 `json:"id,string"`
	ClientID uint64 `json:"client_id,string"`
	Op       string `json:"op"`
}

type Reply struct {
	ID       uint64 `json:"id,string"`
	ClientID uint64 `json:"client_id,string"`
	ViewNum  uint64 `json:"view_num,string"`
	Result   string `json:"result"`
}

type Prepare struct {
	ViewNum   uint64  `json:"view_num,string"`
	OpNum     uint64  `json:"op_num,string"`
	CommitNum uint64  `json:"commit_num,string"`
	Request   Request `json:"request"`
	ReplicaID uint64  `json:"replica_id,string"`
}

type PrepareOK struct {
	ViewNum   uint64 `json:"view_num,string"`
	OpNum     uint64 `json:"op_num,string"`
	ReplicaID uint64 `json:"replica_id,string"`
}

type Commit struct {
	ViewNum   uint64 `json:"view_num,string"`
	CommitNum uint64 `json:"commit_num,string"`
	ReplicaID uint64 `json:"replica_id,string"`
}

type StartViewChange struct {
	ViewNum   uint64 `json:"view_num,string"`
	ReplicaID uint64 `json:"replica_id,string"`
}

type DoViewChange struct {
	ViewNum           uint64   `json:"view_num,string"`
	Logs              log.Logs `json:"logs"`
	LastStableViewNum uint64   `json:"last_stable_view_num,string"`
	OpNum             uint64   `json:"op_num,string"`
	CommitNum         uint64   `json:"commit_num,string"`
	ReplicaID         uint64   `json:"replica_id,string"`
}

type StartView struct {
	ViewNum   uint64   `json:"view_num,string"`
	OpNum     uint64   `json:"op_num,string"`
	CommitNum uint64   `json:"commit_num,string"`
	Logs      log.Logs `json:"logs"`
	ReplicaID uint64   `json:"replica_id,string"`
}

type GetState struct {
	ViewNum   uint64 `json:"view_num,string"`
	OpNum     uint64 `json:"op_num,string"`
	ReplicaID uint64 `json:"replica_id,string"`
}

type NewState struct {
	ViewNum   uint64   `json:"view_num,string"`
	Logs      log.Logs `json:"logs"`
	CommitNum uint64   `json:"commit_num,string"`
	OpNum     uint64   `json:"op_num,string"`
	ReplicaID uint64   `json:"replica_id,string"`
}

type Heartbeat struct{}

// FromReader decodes one event from r with a decoder of its own. The decoder may read past the
// event (encoding/json's Decoder buffers); to read a stream of events, use one decoder for the
// stream and FromDecoder.
func (ev *Event) FromReader(r io.Reader) error {
	return ev.FromDecoder(json.NewDecoder(r))
}

// frameDecoder decodes one frame of dec's stream: its @type and its raw data. It is installed
// by examples/vsrwire's init through SetFrameDecoder (decoding into vsrwire.Frame, a defined
// type with the frame's fields, tags and encoding); it is nil when that package is not linked,
// and FromDecoder then decodes into an unnamed struct type of the same fields and tags.
// frameDecoderMu guards it.
var frameDecoder func(dec *json.Decoder) (uint8, json.RawMessage, error)
var frameDecoderMu = new(sync.Mutex)

// SetFrameDecoder installs f as the frame decoder, unless one is installed (the first stays).
func SetFrameDecoder(f func(dec *json.Decoder) (uint8, json.RawMessage, error)) {
	frameDecoderMu.Lock()
	if frameDecoder == nil {
		frameDecoder = f
	}
	frameDecoderMu.Unlock()
}

// getFrameDecoder returns the installed frame decoder (nil if none).
func getFrameDecoder() func(dec *json.Decoder) (uint8, json.RawMessage, error) {
	frameDecoderMu.Lock()
	f := frameDecoder
	frameDecoderMu.Unlock()
	return f
}

// fromDecoderUnnamed decodes one frame into an unnamed struct type (as released).
func fromDecoderUnnamed(dec *json.Decoder) (uint8, json.RawMessage, error) {
	temp := struct {
		Type EventType       `json:"@type"`
		Data json.RawMessage `json:"data"`
	}{}

	if err := dec.Decode(&temp); err != nil {
		return 0, nil, err
	}

	return uint8(temp.Type), temp.Data, nil
}

// FromDecoder decodes the next event of dec's stream.
func (ev *Event) FromDecoder(dec *json.Decoder) error {
	var t uint8
	var data json.RawMessage
	var err error
	if fd := getFrameDecoder(); fd != nil {
		t, data, err = fd(dec)
	} else {
		t, data, err = fromDecoderUnnamed(dec)
	}
	if err != nil {
		return err
	}

	ev.Type = EventType(t)

	switch ev.Type {
	case EventRequest:
		var v Request
		err = json.Unmarshal(data, &v)
		ev.Data = v
	case EventPrepare:
		var v Prepare
		err = json.Unmarshal(data, &v)
		ev.Data = v
	case EventPrepareOK:
		var v PrepareOK
		err = json.Unmarshal(data, &v)
		ev.Data = v
	case EventCommit:
		var v Commit
		err = json.Unmarshal(data, &v)
		ev.Data = v
	case EventStartViewChange:
		var v StartViewChange
		err = json.Unmarshal(data, &v)
		ev.Data = v
	case EventDoViewChange:
		var v DoViewChange
		err = json.Unmarshal(data, &v)
		ev.Data = v
	case EventStartView:
		var v StartView
		err = json.Unmarshal(data, &v)
		ev.Data = v
	case EventGetState:
		var v GetState
		err = json.Unmarshal(data, &v)
		ev.Data = v
	case EventNewState:
		var v NewState
		err = json.Unmarshal(data, &v)
		ev.Data = v
	case EventHeartbeat:
		var v Heartbeat
		err = json.Unmarshal(data, &v)
		ev.Data = v
	case EventReply:
		var v Reply
		err = json.Unmarshal(data, &v)
		ev.Data = v
	default:
		return ErrInvalidEventType
	}

	if err != nil {
		return err
	}

	return nil
}

func (ev *Event) ToWriter(w io.Writer) error {
	if err := json.NewEncoder(w).Encode(ev); err != nil {
		return err
	}

	return nil
}

func NewNetworkEvent(src ipv4port.IPv4Port, ev *Event) NetworkEvent {
	return NetworkEvent{
		Src:   src,
		Event: ev,
	}
}
