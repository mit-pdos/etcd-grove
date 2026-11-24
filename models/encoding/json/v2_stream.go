// Copyright 2010 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// MODEL: the build constraint goexperiment.jsonv2 is dropped (the model is this build's,
// the default one; the v1 implementation's files, decode.go, encode.go, ..., are not part
// of the model).

package json

import (
	"bytes"
	"errors"
	"io"
)

// A Decoder reads and decodes JSON values from an input stream.
//
// MODEL: the fields of encoding/json/jsontext's decoder that the real Decoder reads through
// (jsontext/decode.go, decodeBuffer): its buffer (buf, with prevStart and prevEnd the bounds of
// the last value read, baseOffset the stream offset of buf[0]) and reader; jsontext's state
// machine is replaced by the codec's scanner.
type Decoder struct {
	r          io.Reader
	buf        []byte
	prevStart  int
	prevEnd    int
	baseOffset int64
	err        error

	// useNumber: UseNumber was called (it changes only decoding into an any, which the codec
	// does not model).
	useNumber bool
}

// NewDecoder returns a new decoder that reads from r.
//
// The decoder introduces its own buffering and may
// read data from r beyond the JSON values requested.
//
// MODEL: jsontext.NewDecoder's check of r (Go's wraps a *bytes.Buffer so that jsontext does not
// read it directly; the model never does).
func NewDecoder(r io.Reader) *Decoder {
	if r == nil {
		panic("jsontext: invalid nil io.Reader")
	}
	return &Decoder{r: r}
}

// UseNumber causes the Decoder to unmarshal a number into an
// interface value as a [Number] instead of as a float64.
func (dec *Decoder) UseNumber() {
	dec.useNumber = true
}

// DisallowUnknownFields causes the Decoder to return an error when the destination
// is a struct and the input contains object keys which do not match any
// non-ignored, exported fields in the destination.
//
// MODEL: not modelled (the codec decodes as Unmarshal does): stuck.
func (dec *Decoder) DisallowUnknownFields() {
	stuck() // MODEL: not modelled (stuck): encoding/json model: Decoder.DisallowUnknownFields (not modelled)
}

// Decode reads the next JSON-encoded value from its
// input and stores it in the value pointed to by v.
//
// See the documentation for [Unmarshal] for details about
// the conversion of JSON into a Go value.
//
// MODEL: the value is read by readValue (jsontext's ReadValue at the top level) and decoded by
// v's own model method (model.go) or the program's codec; an error reading it is sticky, an error decoding it is not (Go's).
func (dec *Decoder) Decode(v any) error {
	if dec.err != nil {
		return dec.err
	}
	c := getCodec()
	b, err := dec.readValue(c)
	if err != nil {
		dec.err = err
		return dec.err
	}
	if u, ok := v.(modelUnmarshaler); ok {
		return u.JSONModelUnmarshal(b, v)
	}
	return c.Unmarshal(b, v)
}

// readValue reads the next top-level value as encoding/json/jsontext's Decoder.ReadValue does
// (jsontext/decode.go): from the end of the last value, more bytes are fetched while the unread
// bytes are whitespace or a proper prefix of a value (the scanner's More; a number at the end of
// the bytes is complete only once a byte follows it or the stream ends); the value is returned
// when complete (Done); a syntax error otherwise. A ',' or ':' where a top-level value starts is
// a syntax error once a byte after the whitespace following it is available or the stream ends
// (jsontext reads on before reporting it: the delimiter check of ReadValue). At the end of the
// stream: io.EOF if only whitespace is left, else io.ErrUnexpectedEOF; a read error: the
// reader's error.
func (dec *Decoder) readValue(c *Codec) ([]byte, error) {
	// jsontext's invalidatePreviousRead: the last value's bytes are no longer kept
	if dec.prevStart < dec.prevEnd {
		dec.prevStart = dec.prevEnd
	}
	pos := dec.prevEnd
	eof := false
	for {
		st, n := c.Scan(dec.buf[pos:], eof)
		if st == scanDone {
			start := pos + skipSpace(dec.buf[pos:])
			end := pos + int(n)
			dec.prevStart = start
			dec.prevEnd = end
			return dec.buf[start:end:end], nil
		}
		if st != scanMore {
			return nil, dec.badStart(pos)
		}
		if eof {
			if skipSpace(dec.buf[pos:]) == len(dec.buf)-pos {
				return nil, io.EOF
			}
			if endsInNumber(dec.buf[pos:]) {
				// jsontext's consumeNumber took the end of the stream as the end of the number
				// and the array or object around it fetches again (its second io.EOF)
				abs := dec.baseOffset + int64(pos)
				err := dec.fetch()
				pos = int(abs - dec.baseOffset)
				if err == nil {
					stuck() // MODEL: not modelled (stuck): encoding/json model: a reader returned data after io.EOF
				}
				if err != io.ErrUnexpectedEOF {
					return nil, err
				}
			}
			return nil, io.ErrUnexpectedEOF
		}
		abs := dec.baseOffset + int64(pos)
		err := dec.fetch()
		pos = int(abs - dec.baseOffset)
		if err == io.ErrUnexpectedEOF {
			eof = true
		} else if err != nil {
			return nil, err
		}
	}
}

// endsInNumber reports whether b (a proper prefix of a value) ends with a digit outside a string:
// a number, complete, inside an array or object.
func endsInNumber(b []byte) bool {
	inStr := false
	i := 0
	for i < len(b) {
		c := b[i]
		if inStr && c == '\\' {
			i++
		} else if c == '"' {
			inStr = !inStr
		}
		i++
	}
	if inStr || len(b) == 0 {
		return false
	}
	c := b[len(b)-1]
	return '0' <= c && c <= '9'
}

// badStart is the syntax error of a value that does not parse at dec.buf[pos:] (after
// whitespace): if it starts with ',' or ':', jsontext first consumes the delimiter and the
// whitespace after it, fetching more while none follows (the error is the same whatever the
// fetch returns: checkDelimBeforeIOError).
func (dec *Decoder) badStart(pos int) error {
	p := pos + skipSpace(dec.buf[pos:])
	if p < len(dec.buf) && (dec.buf[p] == ',' || dec.buf[p] == ':') {
		p = p + 1
		for {
			p = p + skipSpace(dec.buf[p:])
			if p < len(dec.buf) {
				break
			}
			abs := dec.baseOffset + int64(p)
			err := dec.fetch()
			p = int(abs - dec.baseOffset)
			if err != nil {
				break
			}
		}
	}
	return &SyntaxError{msg: "json: invalid JSON input", Offset: dec.baseOffset + int64(p)}
}

// fetch reads at least one byte from the reader into the buffer, as jsontext's
// decodeBuffer.fetch does (jsontext/decode.go): io.ErrUnexpectedEOF if the reader returns
// io.EOF and no byte, its error if it returns another error and no byte (a read returning bytes
// and an error keeps the bytes and drops the error; a read returning neither is retried).
//
// The buffer: 64 bytes at first; before a read, it grows to twice its capacity if it is at most
// 2 KiB and less than half of the stream read up to the end of the last value, or if the bytes
// kept start at its beginning and fill three quarters of it; otherwise the bytes kept (those from
// prevStart on) move to its beginning. The read asks for all of its free space.
func (dec *Decoder) fetch() error {
	if cap(dec.buf) == 0 {
		dec.buf = make([]byte, 0, 64)
	}
	const maxBufferSize = 4 << 10
	const growthSizeFactor = 2
	const growthRateFactor = 2
	grow := cap(dec.buf) <= maxBufferSize/growthSizeFactor
	grow = grow && int64(cap(dec.buf)) < (dec.baseOffset+int64(dec.prevEnd))/growthRateFactor
	grow = grow || (dec.prevStart == 0 && len(dec.buf) >= 3*cap(dec.buf)/4)
	if grow {
		buf := make([]byte, 0, cap(dec.buf)*growthSizeFactor)
		dec.buf = append(buf, dec.buf[dec.prevStart:]...)
	} else {
		n := copy(dec.buf[:cap(dec.buf)], dec.buf[dec.prevStart:])
		dec.buf = dec.buf[:n]
	}
	dec.baseOffset += int64(dec.prevStart)
	dec.prevEnd -= dec.prevStart
	dec.prevStart = 0
	for {
		n, err := dec.r.Read(dec.buf[len(dec.buf):cap(dec.buf)])
		if n > 0 {
			dec.buf = dec.buf[:len(dec.buf)+n]
			return nil
		}
		if err == io.EOF {
			return io.ErrUnexpectedEOF
		}
		if err != nil {
			return err
		}
	}
}

// Buffered returns a reader of the data remaining in the unread buffer,
// which may contain zero or more bytes.
// This is the data already consumed from the input [io.Reader],
// but not yet read by a [Decoder.Decode] or [Decoder.Token] call.
// It may contain bytes that do not form valid JSON as it has not yet
// been validated according to the JSON grammar.
// The exact amount of buffered data is an implementation detail
// of the Decoder and may change over time.
//
// It is the caller's responsibility to concatenate this buffer with
// the remainder of the input Reader to obtain the full sequence
// of bytes after the last decoded JSON value.
//
// The reader is valid until the next call to [Decoder.Decode] or [Decoder.Token].
func (dec *Decoder) Buffered() io.Reader {
	return bytes.NewReader(dec.buf[dec.prevEnd:])
}

// An Encoder writes JSON values to an output stream.
//
// MODEL: no encoding/json/v2 options; the HTML escaping setting is kept (it changes nothing the
// codec writes: the codec writes no string with '<', '>' or '&').
type Encoder struct {
	w          io.Writer
	err        error
	escapeHTML bool

	indentPrefix string
	indentValue  string
}

// NewEncoder returns a new encoder that writes to w.
func NewEncoder(w io.Writer) *Encoder {
	return &Encoder{w: w, escapeHTML: true}
}

// Encode writes the JSON encoding of v to the stream,
// followed by a newline character.
//
// See the documentation for [Marshal] for details about the
// conversion of Go values to JSON.
//
// MODEL: v's own model method or the program's codec encodes (model.go, marshalAny); indentation (SetIndent) is not modelled (stuck).
func (enc *Encoder) Encode(v any) error {
	if enc.err != nil {
		return enc.err
	}
	b, err := marshalAny(v)
	if err != nil {
		return err
	}
	if len(enc.indentPrefix)+len(enc.indentValue) > 0 {
		stuck() // MODEL: not modelled (stuck): encoding/json model: Encoder.SetIndent (indentation is not modelled)
	}
	b = append(b, '\n')

	if _, err := enc.w.Write(b); err != nil {
		enc.err = err
		return err
	}
	return nil
}

// SetIndent instructs the encoder to format each subsequent encoded
// value as if indented by the package-level function Indent(dst, src, prefix, indent).
// Calling SetIndent("", "") disables indentation.
func (enc *Encoder) SetIndent(prefix, indent string) {
	// NOTE: Do not rely on the newer [jsontext.WithIndent] option since
	// the v1 [Indent] behavior has historical bugs that cannot be changed
	// for backward compatibility reasons.
	enc.indentPrefix = prefix
	enc.indentValue = indent
}

// SetEscapeHTML specifies whether problematic HTML characters
// should be escaped inside JSON quoted strings.
// The default behavior is to escape &, <, and > to &, <, and >
// to avoid certain safety problems that can arise when embedding JSON in HTML.
//
// In non-HTML settings where the escaping interferes with the readability
// of the output, SetEscapeHTML(false) disables this behavior.
func (enc *Encoder) SetEscapeHTML(on bool) {
	enc.escapeHTML = on
}

// RawMessage is a raw encoded JSON value.
// It implements [Marshaler] and [Unmarshaler] and can
// be used to delay JSON decoding or precompute a JSON encoding.
//
// MODEL: a type of its own with encoding/json/jsontext.Value's methods (jsontext/value.go; the
// real RawMessage is an alias of jsontext.Value): Clone, String, MarshalJSON and UnmarshalJSON as
// jsontext's; IsValid, Format, Compact, Indent and Canonicalize are stuck (not modelled; they take
// the model's Options, where jsontext's take jsontext.Options); Kind is not part of the model.
type RawMessage []byte

// Clone returns a copy of m.
//
// MODEL: jsontext.Value's Clone.
func (m RawMessage) Clone() RawMessage {
	return bytes.Clone(m)
}

// String returns the string formatting of m.
//
// MODEL: jsontext.Value's String (fmt uses it to print a RawMessage).
func (m RawMessage) String() string {
	if m == nil {
		return "null"
	}
	return string(m)
}

// IsValid reports whether the raw JSON value is syntactically valid.
//
// MODEL: not modelled: stuck.
func (m RawMessage) IsValid(opts ...Options) bool {
	stuck() // MODEL: not modelled (stuck): encoding/json model: RawMessage.IsValid (not modelled)
	return false // (not reached: stuck does not return)
}

// Format formats the raw JSON value in place.
//
// MODEL: not modelled: stuck.
func (m *RawMessage) Format(opts ...Options) error {
	stuck() // MODEL: not modelled (stuck): encoding/json model: RawMessage.Format (not modelled)
	return nil // (not reached: stuck does not return)
}

// Compact removes all whitespace from the raw JSON value.
//
// MODEL: not modelled: stuck.
func (m *RawMessage) Compact(opts ...Options) error {
	stuck() // MODEL: not modelled (stuck): encoding/json model: RawMessage.Compact (not modelled)
	return nil // (not reached: stuck does not return)
}

// Indent reformats the whitespace in the raw JSON value.
//
// MODEL: not modelled: stuck.
func (m *RawMessage) Indent(opts ...Options) error {
	stuck() // MODEL: not modelled (stuck): encoding/json model: RawMessage.Indent (not modelled)
	return nil // (not reached: stuck does not return)
}

// Canonicalize canonicalizes the raw JSON value.
//
// MODEL: not modelled: stuck.
func (m *RawMessage) Canonicalize(opts ...Options) error {
	stuck() // MODEL: not modelled (stuck): encoding/json model: RawMessage.Canonicalize (not modelled)
	return nil // (not reached: stuck does not return)
}

// MarshalJSON returns m as the JSON encoding of m.
//
// MODEL: jsontext.Value's MarshalJSON.
func (m RawMessage) MarshalJSON() ([]byte, error) {
	if m == nil {
		return []byte("null"), nil
	}
	return m, nil
}

// UnmarshalJSON sets *m to a copy of data.
//
// MODEL: jsontext.Value's UnmarshalJSON.
func (m *RawMessage) UnmarshalJSON(data []byte) error {
	if m == nil {
		return errors.New("jsontext.Value: UnmarshalJSON on nil pointer")
	}
	*m = append((*m)[:0], data...)
	return nil
}

// A Token holds a value of one of these types:
//
//   - [Delim], for the four JSON delimiters [ ] { }
//   - bool, for JSON booleans
//   - float64, for JSON numbers
//   - [Number], for JSON numbers
//   - string, for JSON string literals
//   - nil, for JSON null
type Token any

// A Delim is a JSON array or object delimiter, one of [ ] { or }.
//
// MODEL: int32 spelled as such (rune is an alias of int32: the same type), since Goose does not
// take rune.
type Delim int32

func (d Delim) String() string {
	return string(d)
}

// Token returns the next JSON token in the input stream.
// At the end of the input stream, Token returns nil, [io.EOF].
//
// Token guarantees that the delimiters [ ] { } it returns are
// properly nested and matched: if Token encounters an unexpected
// delimiter in the input, it will return an error.
//
// The input stream consists of basic JSON values—bool, string,
// number, and null—along with delimiters [ ] { } of type [Delim]
// to mark the start and end of arrays and objects.
// Commas and colons are elided.
//
// MODEL: not modelled (token-level decoding): stuck.
func (dec *Decoder) Token() (Token, error) {
	stuck() // MODEL: not modelled (stuck): encoding/json model: Decoder.Token (not modelled)
	return nil, nil // (not reached: stuck does not return)
}

// More reports whether there is another element in the
// current array or object being parsed.
//
// MODEL: not modelled (token-level decoding): stuck.
func (dec *Decoder) More() bool {
	stuck() // MODEL: not modelled (stuck): encoding/json model: Decoder.More (not modelled)
	return false // (not reached: stuck does not return)
}

// InputOffset returns the input stream byte offset of the current decoder position.
// The offset gives the location of the end of the most recently returned token
// and the beginning of the next token.
//
// MODEL: jsontext's InputOffset (the end of the last value read); Go's adjustments after More
// and Token do not arise (those panic).
func (dec *Decoder) InputOffset() int64 {
	return dec.baseOffset + int64(dec.prevEnd)
}
