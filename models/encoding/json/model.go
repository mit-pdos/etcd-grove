// MODEL: this file is the model's own (not in Go's encoding/json).
//
// Package json here is a model of Go 1.27.3's encoding/json (models/README.md): the package as
// the toolchain builds it by default (GOEXPERIMENT jsonv2 on: the v2_*.go files, the v1 API over
// encoding/json/v2), with every exported name kept and Go's code wherever it does not use
// reflection or encoding/json/v2 and encoding/json/jsontext (the error types, Number, HTMLEscape,
// the docs); the places changed are marked MODEL.
//
// The claim (trusted): every behavior of Go's encoding/json, as the program observes it, is a
// behavior of this model, for a program whose codec (below) covers its types. Where the model
// does not model Go's behavior it panics with a value that has a NotModelled method, so that a
// proof that the program does not panic shows it never gets there. Observed means: the values
// returned and stored (only whether an error is nil, and the identity of io.EOF and
// io.ErrUnexpectedEOF from a Decoder, not an error's type or message), the bytes written to an
// Encoder's writer and how they are split into Write calls, and the Read calls a Decoder makes
// (each one's buffer length, and when it is made), for readers on which a Read after io.EOF
// returns io.EOF again and changes nothing (net.Conn, files, strings and bytes readers): the
// real Decoder may call Read once more after io.EOF than the model (a number completed by the end
// of the stream inside an unfinished array or object).
//
// What replaces reflection is, for a value whose type has them, the methods jsongen emits into the
// type's own package (the per-type dispatch, below), and otherwise a Codec, which the program
// registers (SetCodec), generated for the program's types by models/json/jsongen.py (the trusted generator; its core jsongen_core.py says,
// per kind of type, which of encoding/json's rules it reproduces, with citations):
//   - Marshal: the encoding of a value of one of the program's types (or a pointer to one, or a
//     basic value, or nil), as encoding/json writes it; another value panics.
//   - Unmarshal: decoding one valid JSON value into a pointer to one of the program's types, as
//     encoding/json decodes it; a value outside the codec's subset (a string with an escape
//     sequence, an array into a non-nil slice, a value into an any) panics.
//   - Scan: the JSON scanner (models.lab/jsoncodec.Scan, tested against encoding/json): where the
//     JSON value at the start of a byte slice ends, or that more bytes are needed, or a syntax
//     error. A standard-library package cannot import the module that holds it, so it comes with
//     the codec.
//
// The Decoder (v2_stream.go) reads as Go's does over encoding/json/jsontext's decoder: the same
// buffer (64 bytes at first, grown and compacted by jsontext's rules, so every Read asks for the
// same length at the same point), the same top-level framing of a stream of values (whitespace
// between them, none needed after an array, object, string or literal, io.EOF at the end of the
// stream with only whitespace left, io.ErrUnexpectedEOF inside a value, the reader's own error
// otherwise; every such error sticky). The Encoder writes each value's encoding and a newline in
// one Write, a write error sticky (Go's).
//
// Not modelled (a panic): MarshalIndent, Indent, Compact, Encoder.SetIndent with a non-empty
// prefix or indent, Decoder.Token, Decoder.More, Decoder.DisallowUnknownFields, encoding/json/v2's
// options (DefaultOptionsV1, ...), and every type and value outside the codec's subset. Not part
// of the model: RawMessage's methods other than MarshalJSON and UnmarshalJSON (the real
// RawMessage is an alias of encoding/json/jsontext.Value: reflection on a RawMessage, fmt's %T
// among it, sees another type), Number's MarshalJSONTo and UnmarshalJSONFrom.
package json

import "sync"

// Codec is the model's stand-in for reflection: a program's generated functions (not in Go's
// encoding/json; models/json/jsongen.py writes them and their registration, RegisterJSON).
type Codec struct {
	// Marshal is encoding/json's Marshal for the program's types.
	Marshal func(v any) ([]byte, error)
	// Unmarshal is encoding/json's Unmarshal for the program's types, of data that is one valid
	// JSON value with whitespace around it.
	Unmarshal func(data []byte, v any) error
	// Scan is models.lab/jsoncodec.Scan: (0, n) if b starts with one complete JSON value ending at
	// n (whitespace before it; a number is complete at the first byte that cannot continue it, or
	// at the end of b if eof), (1, _) if b is whitespace or a proper prefix of a value, (2, _) on a
	// syntax error (nesting deeper than 10000 among them).
	Scan func(b []byte, eof bool) (uint64, uint64)
}

// notModelled is the value the model panics with where it does not model Go's behavior.
type notModelled string

// NotModelled marks the value as the models' panic.
func (notModelled) NotModelled() {}

var codecMu sync.Mutex
var codec *Codec

// SetCodec registers the program's codec (generated by jsongen.py). A second registration
// panics: a program has one codec, for all its types.
func SetCodec(c *Codec) {
	codecMu.Lock()
	if codec != nil {
		codecMu.Unlock()
		panic(notModelled("encoding/json model: a second codec registered"))
	}
	codec = c
	codecMu.Unlock()
}

// The per-type dispatch (MODEL: not in Go's encoding/json). jsongen's same-package mode
// (models/json/jsongen_core.py, "THE SAME-PACKAGE METHODS") emits these methods into a named type's
// own package, in a model build only (build tag goose or netmodel, through goose's -overlay): on T,
// JSONModelMarshal, and on *T, JSONModelMarshalPtr and JSONModelUnmarshal, each encoding/json's
// Marshal or Unmarshal for a value of type exactly T or *T (any other dynamic type, which can have
// the methods only by promotion through embedding, is not modelled: a panic). Marshal, Unmarshal,
// Encoder.Encode and Decoder.Decode call a value's method when its dynamic type has one, and the
// registered codec otherwise (nil and the program's unnamed types). The names are reserved: no
// code other than the generated files declares or calls them (the gates).
type modelMarshalerPtr interface {
	JSONModelMarshalPtr(v any) ([]byte, error)
}

type modelMarshaler interface {
	JSONModelMarshal(v any) ([]byte, error)
}

type modelUnmarshaler interface {
	JSONModelUnmarshal(data []byte, v any) error
}

// marshalAny is Marshal: by v's own method if its dynamic type has one (JSONModelMarshalPtr first:
// a *T has both, and only that one is nil-safe), else by the registered codec.
func marshalAny(v any) ([]byte, error) {
	if m, ok := v.(modelMarshalerPtr); ok {
		return m.JSONModelMarshalPtr(v)
	}
	if m, ok := v.(modelMarshaler); ok {
		return m.JSONModelMarshal(v)
	}
	return getCodec().Marshal(v)
}

func getCodec() *Codec {
	codecMu.Lock()
	c := codec
	codecMu.Unlock()
	if c == nil {
		panic(notModelled("encoding/json model: no codec registered (the program's generated codec registers it: RegisterJSON)"))
	}
	return c
}

// The scanner's results (jsoncodec's Done, More, Bad).
const (
	scanDone uint64 = 0
	scanMore uint64 = 1
)

func isSpace(c byte) bool {
	return c == ' ' || c == '\t' || c == '\n' || c == '\r'
}

// skipSpace returns the number of whitespace bytes at the start of b.
func skipSpace(b []byte) int {
	i := 0
	for i < len(b) && isSpace(b[i]) {
		i++
	}
	return i
}

// valid reports whether data is one JSON value with whitespace around it (Go's Valid).
func valid(c *Codec, data []byte) bool {
	st, n := c.Scan(data, true)
	if st != scanDone {
		return false
	}
	return skipSpace(data[n:]) == len(data)-int(n)
}
