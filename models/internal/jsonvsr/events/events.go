// Copied from go-vsr (github.com/tangledbytes/go-vsr, Apache License 2.0), the dsverify
// verification fork at 215992d, pkg/events/events.go: the event types (NetworkEvent and NewNetworkEvent, which
// name the network's address type, left out).
// A test input of the encoding/json model: what the vsr-net kit sends over TCP as JSON
// (../json.toml; the stream tests in ../../jsonstreamtest).

package events

import (
	"errors"

	"models.lab/internal/jsonvsr/log"
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
