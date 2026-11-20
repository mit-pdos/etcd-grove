// Package jsondifftest holds the types of the differential test of the encoding/json codec
// generator (models/json/jsongen.py, json.toml; the codec and its test generated into codec/): a frame with
// a type and a raw payload, payloads of the kinds the codec decodes (from dsverify-lab's
// harness/rpcmodel/difftest, 348a866), a named basic type, and a frame whose payload is an `any`
// (encoded by its dynamic type, not decodable).
package jsondifftest

import "encoding/json"

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

type Kind uint8

type Event struct {
	Kind Kind        `json:"@kind"`
	Seq  uint64      `json:"seq,string"`
	Data interface{} `json:"data"`
}
