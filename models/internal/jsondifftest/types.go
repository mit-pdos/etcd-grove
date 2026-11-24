// Package jsondifftest holds the types of a regression test of the encoding/json codec generator
// (models/json/jsongen.py, json.toml; the codec and its test generated into codec/): a frame with
// a type and a raw payload, payloads of the kinds the codec decodes (from dsverify-lab's
// harness/rpcmodel/difftest, 348a866), a named basic type, a frame whose payload is an `any`
// (encoded by its dynamic type; decoding into it is not modelled), and a struct of every accepted
// field kind and tag form (signed integers, omitempty, string, ignored and unexported fields, a
// recursive slice).
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

type Name string

type Flag bool

type Tree []Tree

type All struct {
	I     int
	I8    int8            `json:"i8,omitempty"`
	I16   int16           `json:",string"`
	I32   int32           `json:"i32,string,omitempty"`
	I64   int64           `json:"i-64"`
	U     uint            `json:"u,omitempty,string"`
	U16   uint16          `json:"U16"`
	Name  Name            `json:"name,omitempty"`
	Flag  Flag            `json:"flag,omitempty"`
	Items []Item          `json:"items,omitempty"`
	Raw   json.RawMessage `json:"raw,omitempty"`
	Any   any             `json:"any,omitempty"`
	Body  Body            `json:"body,omitempty"`
	Tree  Tree            `json:"tree"`
	Skip  string          `json:"-"`
	Punct string          `json:"a.b:c/d$e"`
	hide  int
}
