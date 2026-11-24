// Copied from go-vsr (github.com/tangledbytes/go-vsr, Apache License 2.0), the dsverify
// verification fork at 215992d, pkg/events/wire/wire.go: as it is (the wire
// format: one Encoder per event written, one Decoder per event read).
// A test input of the encoding/json model: what the vsr-net kit sends over TCP as JSON
// (../json.toml; the stream tests in ../../jsonstreamtest).

// Package wire is the JSON wire format of events (moved out of package events in the
// verification fork; only the TCP network and the simulator use it).
package wire

import (
	"encoding/json"
	"io"

	"models.lab/internal/jsonvsr/events"
)

// Decode reads one event from r (the JSON wire format).
func Decode(r io.Reader, ev *events.Event) error {
	temp := struct {
		Type events.EventType `json:"@type"`
		Data json.RawMessage  `json:"data"`
	}{}

	if err := json.NewDecoder(r).Decode(&temp); err != nil {
		return err
	}

	ev.Type = temp.Type
	var err error

	switch ev.Type {
	case events.EventRequest:
		var v events.Request
		err = json.Unmarshal(temp.Data, &v)
		ev.Data = v
	case events.EventPrepare:
		var v events.Prepare
		err = json.Unmarshal(temp.Data, &v)
		ev.Data = v
	case events.EventPrepareOK:
		var v events.PrepareOK
		err = json.Unmarshal(temp.Data, &v)
		ev.Data = v
	case events.EventCommit:
		var v events.Commit
		err = json.Unmarshal(temp.Data, &v)
		ev.Data = v
	case events.EventStartViewChange:
		var v events.StartViewChange
		err = json.Unmarshal(temp.Data, &v)
		ev.Data = v
	case events.EventDoViewChange:
		var v events.DoViewChange
		err = json.Unmarshal(temp.Data, &v)
		ev.Data = v
	case events.EventStartView:
		var v events.StartView
		err = json.Unmarshal(temp.Data, &v)
		ev.Data = v
	case events.EventGetState:
		var v events.GetState
		err = json.Unmarshal(temp.Data, &v)
		ev.Data = v
	case events.EventNewState:
		var v events.NewState
		err = json.Unmarshal(temp.Data, &v)
		ev.Data = v
	case events.EventHeartbeat:
		var v events.Heartbeat
		err = json.Unmarshal(temp.Data, &v)
		ev.Data = v
	case events.EventReply:
		var v events.Reply
		err = json.Unmarshal(temp.Data, &v)
		ev.Data = v
	default:
		return events.ErrInvalidEventType
	}

	if err != nil {
		return err
	}

	return nil
}

// Encode writes ev to w (the JSON wire format).
func Encode(w io.Writer, ev *events.Event) error {
	if err := json.NewEncoder(w).Encode(ev); err != nil {
		return err
	}

	return nil
}
