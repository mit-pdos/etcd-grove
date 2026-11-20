// Package gob is the dsverify lab's model of the part of Go's encoding/gob (Go 1.27.3) that a
// program uses to send values over a byte stream: NewEncoder and Encode, NewDecoder and Decode
// (SwiftPaxos's MSync, kits/swift-net). A kit opts in (kit.toml [rpc] gob = true): goose and the
// model build then use a GOROOT whose encoding/gob is this package (harness/rpcmodel/goroot.sh
// OUT gob), and the kit's generated registerRPC hands it the kit's codec (the net/rpc model's,
// generated from kit.toml's [rpc] types and tested there against real gob).
//
// The model's wire format is its own: a value is one frame, its encoding's length (8 bytes,
// little-endian) and the codec's encoding (the value's type tag first), written with one Write
// to the encoder's writer; Decode reads exactly one frame from the decoder's reader (io.ReadFull)
// and decodes it into the target as gob would (the codec's Decode: an error if gob would refuse
// the encoded type). Every node of the model build uses the model, so the format need only
// round-trip. Go's gob also sends a value's type before its first value on an encoder and
// reads exactly the messages it needs; the model has no type messages (the codec's tag names the
// type) and reads exactly its frame. Not modeled: Register, an Encoder's or Decoder's later
// values sharing the first one's type messages (every SwiftPaxos MSync uses a fresh encoder and
// decoder), and frames over MaxFrame bytes (Decode refuses them).
package gob

import (
	"errors"
	"io"
	"sync"
)

// Codec is the kit's encoder and decoder of its listed types (the net/rpc model's Encode and
// Decode, harness/rpcmodel/src/net/rpc/codec.go): Encode(v) is v's type tag and encoding (v a
// listed type or a non-nil pointer to one; panics otherwise); Decode(data, ptr) decodes data
// into *ptr as gob would (ptr a non-nil pointer to a listed type whose value is zero).
type Codec struct {
	Encode func(v interface{}) []byte
	Decode func(data []byte, ptr interface{}) error
}

var codecMu sync.Mutex
var codec *Codec

// SetCodec registers the kit's codec; the first registration stays. It is not in Go's gob: the
// kit's generated registerRPC (model build only) calls it.
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
		panic("encoding/gob model: no codec registered (the kit's registerRPC)")
	}
	return c
}

// MaxFrame bounds a frame's encoding (Go's gob refuses messages over tooBig, 1 GiB on 64-bit
// machines).
const MaxFrame uint64 = 1 << 30

var errTooBig = errors.New("gob: decoder: message too big")

// An Encoder writes values to a writer.
type Encoder struct {
	w io.Writer
}

// NewEncoder returns a new encoder that will transmit on the io.Writer.
func NewEncoder(w io.Writer) *Encoder {
	return &Encoder{w: w}
}

// Encode transmits the value e: one frame, written with one Write. The error is the Write's.
func (enc *Encoder) Encode(e interface{}) error {
	body := getCodec().Encode(e)
	n := uint64(len(body))
	frame := make([]byte, 8, 8+n)
	for i := uint64(0); i < 8; i++ {
		frame[i] = byte(n >> (8 * i))
	}
	frame = append(frame, body...)
	_, err := enc.w.Write(frame)
	return err
}

// A Decoder reads values from a reader.
type Decoder struct {
	r io.Reader
}

// NewDecoder returns a new decoder that reads from the io.Reader.
func NewDecoder(r io.Reader) *Decoder {
	return &Decoder{r: r}
}

// Decode reads the next frame from the reader and stores its value in the data represented by
// the pointer e. The error is the read's (io.EOF before any byte, io.ErrUnexpectedEOF within a
// frame, or the reader's), errTooBig, or the codec's.
func (dec *Decoder) Decode(e interface{}) error {
	var hdr [8]byte
	if _, err := io.ReadFull(dec.r, hdr[:]); err != nil {
		return err
	}
	n := uint64(0)
	for i := uint64(0); i < 8; i++ {
		n = n | uint64(hdr[i])<<(8*i)
	}
	if n > MaxFrame {
		return errTooBig
	}
	body := make([]byte, n)
	if _, err := io.ReadFull(dec.r, body); err != nil {
		if err == io.EOF {
			// the stream ended after the frame's length: inside the value, as Go's says
			return io.ErrUnexpectedEOF
		}
		return err
	}
	return getCodec().Decode(body, e)
}
