// Package json is the dsverify lab's model of Go's encoding/json (Go 1.27.3), substituted for
// the real package as net/rpc and log are (harness/rpcmodel/goroot.sh; notes/vsr-net.md). Goose
// translates it in place of the real package, and the harness proves its specs once
// (harness/lean/Harness/Proof/encoding/json).
//
// Real encoding/json works by reflection, which Goose does not translate. In its place, a kit
// registers a codec generated from its kit.toml's [json] section (harness/kitgen/jsongen.py) for
// exactly the Go types its program encodes and decodes: SetCodec (model only; the kit's generated
// registerJSON calls it under the build tag rpcmodel, and is a no-op in the real build). The
// codec's encoders write the bytes real encoding/json writes, and its decoders decode as real
// encoding/json does, for those types; its scanner (dsverify.lab/harness/jsoncodec.Scan) finds
// where a JSON value ends. The trusted claim, tested against real encoding/json by the kit's
// generated json_gen_test.go and by rpcmodel/difftest, is that for the program's calls the model
// returns what real encoding/json returns, consumes from a Decoder's reader at most what real
// encoding/json may, and writes what it writes; where the model cannot (a string with an escape
// or a non-ASCII byte, HTML characters, decoding into a non-nil slice, a type not listed), it
// panics: stricter than Go, never more permissive. Error values are not modeled beyond nil or
// not (and io.EOF, io.ErrUnexpectedEOF and a Read error, which a Decoder returns as such).
//
// The subset: Marshal, Unmarshal, Valid, NewEncoder, (*Encoder).Encode, NewDecoder,
// (*Decoder).Decode, RawMessage (with its MarshalJSON and UnmarshalJSON), Marshaler,
// Unmarshaler, SyntaxError.
package json

import "sync"

// Codec is the model's stand-in for reflection: a kit's generated functions (not in Go's
// encoding/json).
//
//   - Marshal(v): v's encoding as real Marshal gives it, for v of a listed type or a pointer to
//     one (calling a listed type's MarshalJSON as Marshal does), or a MarshalJSON method's error
//     (or its output's: invalid JSON). Panics for any other v.
//   - Unmarshal(data, v): decodes data, one valid JSON value with whitespace around it (Scan's
//     Done, then only whitespace), into v as real Unmarshal does: v a non-nil pointer to a
//     listed type; a nil pointer or a non-pointer is real Unmarshal's error. Panics otherwise.
//   - Scan(b, eof): jsoncodec.Scan: (0, n) if b starts with one complete JSON value ending at n
//     (whitespace before it), (1, _) if more bytes are needed, (2, _) on a syntax error.
type Codec struct {
	Marshal   func(v interface{}) ([]byte, error)
	Unmarshal func(data []byte, v interface{}) error
	Scan      func(b []byte, eof bool) (uint64, uint64)
}

var codecMu sync.Mutex
var codec *Codec

// SetCodec registers the kit's codec; the first registration stays.
func SetCodec(c *Codec) {
	codecMu.Lock()
	if codec == nil {
		codec = c
	}
	codecMu.Unlock()
}

func getCodec() *Codec {
	codecMu.Lock()
	c := codec
	codecMu.Unlock()
	if c == nil {
		panic("encoding/json model: no codec registered (the kit's registerJSON)")
	}
	return c
}

// The scanner's results (jsoncodec's Done, More, Bad).
const (
	scanDone uint64 = 0
	scanMore uint64 = 1
)

// Marshaler is the interface of a type that encodes itself.
type Marshaler interface {
	MarshalJSON() ([]byte, error)
}

// Unmarshaler is the interface of a type that decodes itself.
type Unmarshaler interface {
	UnmarshalJSON([]byte) error
}

// RawMessage is a raw encoded JSON value (Go's methods: MarshalJSON returns it, or "null" if it
// is nil; UnmarshalJSON copies its input into it, reusing its storage).
type RawMessage []byte

func (m RawMessage) MarshalJSON() ([]byte, error) {
	if m == nil {
		return []byte("null"), nil
	}
	return m, nil
}

func (m *RawMessage) UnmarshalJSON(data []byte) error {
	if m == nil {
		return &SyntaxError{msg: "json.RawMessage: UnmarshalJSON on nil pointer"}
	}
	*m = append((*m)[0:0], data...)
	return nil
}

// SyntaxError is the error for input that is not valid JSON (the model keeps no offset).
type SyntaxError struct {
	msg string
}

func (e *SyntaxError) Error() string {
	return e.msg
}

// Marshal returns v's JSON encoding.
func Marshal(v interface{}) ([]byte, error) {
	return getCodec().Marshal(v)
}

func isSpace(c byte) bool {
	return c == ' ' || c == '\t' || c == '\n' || c == '\r'
}

// allSpace reports whether b is only whitespace.
func allSpace(b []byte) bool {
	for _, c := range b {
		if !isSpace(c) {
			return false
		}
	}
	return true
}

// valid reports whether data is one JSON value with whitespace around it.
func valid(c *Codec, data []byte) bool {
	st, n := c.Scan(data, true)
	return st == scanDone && allSpace(data[n:])
}

// Valid reports whether data is one valid JSON value (with whitespace around it).
func Valid(data []byte) bool {
	return valid(getCodec(), data)
}

// Unmarshal decodes data into v: a syntax error (nothing decoded) unless data is one valid JSON
// value, else the codec's decoding.
func Unmarshal(data []byte, v interface{}) error {
	c := getCodec()
	if !valid(c, data) {
		return &SyntaxError{msg: "json: invalid JSON input"}
	}
	return c.Unmarshal(data, v)
}
