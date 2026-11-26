// Package vsrwire is a named type for go-vsr's wire frame (added by the kit, not part of go-vsr).
//
// events.(*Event).FromReader decoded each message into an unnamed struct type with field tags,
// which Goose cannot translate (ISSUES.md, G1). Frame has the same fields, tags and encoding
// (Type is the uint8 under events.EventType). This package installs, at init, the hook
// events' frame decoder (events.SetFrameDecoder) that decodes a frame into a Frame (vsrwire imports events, not the
// converse: events is initialized before vsrwire). The kit's encoding/json codec lists both
// types.
package vsrwire

import (
	"encoding/json"

	"github.com/tangledbytes/go-vsr/pkg/events"
)

// Frame is one message on the wire: its type and its payload, undecoded.
type Frame struct {
	Type uint8           `json:"@type"`
	Data json.RawMessage `json:"data"`
}

func init() {
	events.SetFrameDecoder(decodeFrame)
}

// decodeFrame decodes one frame of dec's stream into a Frame.
func decodeFrame(dec *json.Decoder) (uint8, json.RawMessage, error) {
	f := Frame{}
	if err := dec.Decode(&f); err != nil {
		return 0, nil, err
	}
	return f.Type, f.Data, nil
}
