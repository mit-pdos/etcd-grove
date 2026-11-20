package difftest

import "encoding/json"

// Msg, Body and Item are the encoding/json model's test types (json_test.go): a frame with a type
// and a raw payload, as go-vsr's wire format, and payloads of the kinds the codec decodes.
type Msg struct {
	Type uint8           `json:"@type"`
	Data json.RawMessage `json:"data"`
}

type Body struct {
	N  uint64 `json:"n,string"`
	S  string `json:"s"`
	Ok bool   `json:"ok"`
	K  uint32 `json:"k"`
	L  []Item `json:"l"`
}

type Item struct {
	D string `json:"d"`
}
