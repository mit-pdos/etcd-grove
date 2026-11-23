/*
 *
 * Copyright 2026 the etcd-grove authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 */

package grpc

// MODEL: the model's wire (notes/specs-only/tcp-extension-design.md, section 4.2, with one stream
// per connection). A connection carries one RPC. The client writes HTTP/2's 24-byte client preface
// (so that cmux's HTTP2() matcher, which reads exactly it, still matches) and the server answers
// with its preface (one settings frame, as HTTP/2's SETTINGS) before the client sends anything
// else (grpc-go's client writes streams only on a connection whose server preface arrived); then
// frames:
//
//	frame   = kind:u8 body
//	head, header, trailer: length:u32be fields     (a header block; length bounded before reading)
//	header, trailer:       length:u32be            (a length over maxHeaderBlock, no fields: a block
//	                                                the server did not send, over the client's limit)
//	fields  = count:u32be (nameLen:u32be name valueLen:u32be value)*
//	data:    flag:u8 length:u32be message           (one gRPC length-prefixed message, as on HTTP/2)
//	reset:   code:u32be                             (an HTTP/2 error code)
//	close, cancel: nothing
//
// Client to server: head (the request's HTTP/2 header fields, as grpc-go's createHeaderFields
// makes them), data*, close (END_STREAM), cancel (RST_STREAM CANCEL). Server to client: header
// (the response's header fields), data*, trailer (its trailer fields; or the only header block of
// a trailers-only response), reset (RST_STREAM with its error code: REFUSED_STREAM for a stream
// that was not dispatched, which is also how the model shows a GOAWAY whose last stream id is
// below the stream; CANCEL when the server's deadline for the stream passes). Each side's writes are serialized, and a writer gives the
// connection up after a failed write.
//
// The header fields are grpc-go's own (":path", "content-type", "grpc-timeout", "grpc-status",
// "grpc-message", the metadata, ...), made and read by grpc-go's own code
// (model_http_util.go), so metadata, timeouts and status messages arrive as grpc-go delivers them.
// What the wire drops of HTTP/2 (stream ids, multiplexing, flow control, HPACK, settings, pings,
// GOAWAY) the program cannot observe: see model_transport.go.

import (
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"net"

	"google.golang.org/grpc/codes"
)

// The frame kinds.
const (
	frameHead     byte = 1 // client: the request's header fields
	frameData     byte = 2 // either: one gRPC message
	frameClose    byte = 3 // client: no more request messages
	frameCancel   byte = 4 // client: the client gave the stream up
	frameHeader   byte = 5 // server: the response's header fields
	frameTrailer  byte = 6 // server: the trailer fields; the stream's end
	frameReset    byte = 7 // server: RST_STREAM with an HTTP/2 error code; the stream's end
	frameSettings byte = 8 // server: its preface (HTTP/2's SETTINGS), right after the client's
)

// maxHeaderBlock bounds a header block's length (grpc-go's default limit on a received header
// list, defaultClientMaxHeaderListSize and defaultServerMaxHeaderListSize, 16 MiB; HPACK's
// per-field overhead aside).
const maxHeaderBlock = 16 << 20

// headerField is an HTTP/2 header field (hpack.HeaderField's name and value).
type headerField struct {
	Name, Value string
}

var errMalformedFrame = errors.New("grpc: malformed frame")

// errHeaderListTooLarge is a header block over the reader's limit (http2.ConnectionError's message
// for the hpack decoder's string length limit, which a field over the limit hits first).
var errHeaderListTooLarge = errors.New("connection error: COMPRESSION_ERROR")

// readFull reads exactly len(b) bytes from c (io.ReadFull's contract: io.ErrUnexpectedEOF if the
// connection ends inside them, io.EOF if before any).
func readFull(c net.Conn, b []byte) error {
	n := 0
	for n < len(b) {
		k, err := c.Read(b[n:])
		n += k
		if n == len(b) {
			return nil
		}
		if err != nil {
			if err == io.EOF && n > 0 {
				return io.ErrUnexpectedEOF
			}
			return err
		}
	}
	return nil
}

// readFrameKind reads a frame's kind.
func readFrameKind(c net.Conn) (byte, error) {
	var k [1]byte
	if err := readFull(c, k[:]); err != nil {
		return 0, err
	}
	return k[0], nil
}

// MODEL: a header list's size bounds what is sent (finding F1, notes/phase7-plan.md, section 0a:
// appendHeaderBlock writes lengths as uint32s, so a block of 4 GiB or more would be misframed). A
// receiver of grpc-go v1.84.0 refuses a header list over its limit (defaultClientMaxHeaderListSize,
// defaultServerMaxHeaderListSize: 16 MiB) as x/net/http2 counts it (hpack.HeaderField.Size: name,
// value and 32 per field; Framer.readMetaFrame): such a list never reaches the receiving program,
// whichever way it fails (a FRAME_SIZE_ERROR reset of a truncated list, a COMPRESSION_ERROR or
// PROTOCOL_ERROR connection error of a field or a continuation over it; measured,
// internal/grpcdifftest/headerlimit_test.go). So the model's writers check the list's size before
// writing: the client ends its stream unsent (newClientTransportStream), the server writes the
// over-limit marker instead (appendOversizedBlock), on which the client's reader fails the stream as
// grpc-go's does. A peer's smaller limit (the MaxHeaderListSize options) is not modelled: the options
// are ignored, as before.

// headerListTooLarge reports whether fields' header list is over the receiver's limit (its size
// counted as HTTP/2 does, stopping once over the limit: each addition is of one length to a sum
// within the limit, so the sum cannot overflow).
func headerListTooLarge(fields []headerField) bool {
	var sz uint64
	for _, f := range fields {
		sz += 32 + uint64(len(f.Name))
		if sz > maxHeaderBlock {
			return true
		}
		sz += uint64(len(f.Value))
		if sz > maxHeaderBlock {
			return true
		}
	}
	return false
}

// appendOversizedBlock appends the marker of a header or trailer block over the receiver's limit,
// which is not sent: its kind and a length over maxHeaderBlock, which the reader refuses before
// reading any field.
func appendOversizedBlock(b []byte, kind byte) []byte {
	b = append(b, kind)
	return binary.BigEndian.AppendUint32(b, maxHeaderBlock+1)
}

// appendHeaderBlock appends a head, header or trailer frame carrying fields, whose list is not over
// the limit (every caller checks headerListTooLarge first), so that every length fits its uint32.
func appendHeaderBlock(b []byte, kind byte, fields []headerField) []byte {
	n := 4
	for _, f := range fields {
		n += 8 + len(f.Name) + len(f.Value)
	}
	b = append(b, kind)
	b = binary.BigEndian.AppendUint32(b, uint32(n))
	b = binary.BigEndian.AppendUint32(b, uint32(len(fields)))
	for _, f := range fields {
		b = binary.BigEndian.AppendUint32(b, uint32(len(f.Name)))
		b = append(b, f.Name...)
		b = binary.BigEndian.AppendUint32(b, uint32(len(f.Value)))
		b = append(b, f.Value...)
	}
	return b
}

// readHeaderBlock reads a header block's body (after its kind), its length checked before
// anything is allocated.
func readHeaderBlock(c net.Conn) ([]headerField, error) {
	var lb [4]byte
	if err := readFull(c, lb[:]); err != nil {
		return nil, err
	}
	n := binary.BigEndian.Uint32(lb[:])
	if n > maxHeaderBlock {
		return nil, errHeaderListTooLarge
	}
	if n < 4 {
		return nil, errMalformedFrame
	}
	p := make([]byte, n)
	if err := readFull(c, p); err != nil {
		return nil, err
	}
	count := binary.BigEndian.Uint32(p[0:4])
	p = p[4:]
	var fields []headerField
	for i := uint32(0); i < count; i++ {
		name, rest, ok := cutString(p)
		if !ok {
			return nil, errMalformedFrame
		}
		value, rest2, ok := cutString(rest)
		if !ok {
			return nil, errMalformedFrame
		}
		fields = append(fields, headerField{Name: name, Value: value})
		p = rest2
	}
	if len(p) != 0 {
		return nil, errMalformedFrame
	}
	return fields, nil
}

// cutString splits a length-prefixed string off p.
func cutString(p []byte) (string, []byte, bool) {
	if len(p) < 4 {
		return "", nil, false
	}
	n := binary.BigEndian.Uint32(p[0:4])
	if uint64(n) > uint64(len(p)-4) {
		return "", nil, false
	}
	return string(p[4 : 4+n]), p[4+n:], true
}

// appendData appends a data frame: the message's 5-byte gRPC header and its payload.
func appendData(b []byte, hdr []byte, payload []byte) []byte {
	b = append(b, frameData)
	b = append(b, hdr...)
	return append(b, payload...)
}

// recvMsg is an item of a stream's receive queue: a message (its 5-byte header, and its payload
// unless its length is over the receiver's limit, which the parser then reports without the
// payload ever being read into memory), or the stream's end (err: io.EOF at a normal end, else
// the error the reader gets).
type recvMsg struct {
	hdr  [5]byte
	data []byte
	err  error
}

// readData reads a data frame's body (after its kind). A message longer than max is not read into
// memory: its payload is read and dropped in pieces (the stream keeps going; the receiver's
// parser fails on the length, as grpc-go's does before reading the message).
func readData(c net.Conn, max int) (recvMsg, error) {
	var m recvMsg
	if err := readFull(c, m.hdr[:]); err != nil {
		return m, err
	}
	n := binary.BigEndian.Uint32(m.hdr[1:])
	if int64(n) > int64(max) {
		var scratch [4096]byte
		left := int64(n)
		for left > 0 {
			k := int64(len(scratch))
			if left < k {
				k = left
			}
			if err := readFull(c, scratch[:k]); err != nil {
				return m, err
			}
			left -= k
		}
		return m, nil
	}
	m.data = make([]byte, n)
	if err := readFull(c, m.data); err != nil {
		return m, err
	}
	return m, nil
}

// HTTP/2 error codes the model's server sends (http2.ErrCode).
const (
	errCodeNo            uint32 = 0x0
	errCodeProtocol      uint32 = 0x1
	errCodeStreamClosed  uint32 = 0x5
	errCodeRefusedStream uint32 = 0x7
	errCodeCancel        uint32 = 0x8
)

// http2ErrCodeNames are http2.ErrCode's String() values.
var http2ErrCodeNames = []string{"NO_ERROR", "PROTOCOL_ERROR", "INTERNAL_ERROR", "FLOW_CONTROL_ERROR",
	"SETTINGS_TIMEOUT", "STREAM_CLOSED", "FRAME_SIZE_ERROR", "REFUSED_STREAM", "CANCEL",
	"COMPRESSION_ERROR", "CONNECT_ERROR", "ENHANCE_YOUR_CALM", "INADEQUATE_SECURITY", "HTTP_1_1_REQUIRED"}

// http2ErrConvTab is transport's: the status code of a RST_STREAM's error code.
var http2ErrConvTab = []codes.Code{codes.Internal, codes.Internal, codes.Internal,
	codes.ResourceExhausted, codes.Internal, codes.Internal, codes.Internal, codes.Unavailable,
	codes.Canceled, codes.Internal, codes.Internal, codes.ResourceExhausted, codes.PermissionDenied,
	codes.Internal}

// errCodeString is http2.ErrCode.String.
func errCodeString(c uint32) string {
	if c < uint32(len(http2ErrCodeNames)) {
		return http2ErrCodeNames[c]
	}
	return fmt.Sprintf("unknown error code 0x%x", c)
}

// appendReset appends a reset frame.
func appendReset(b []byte, code uint32) []byte {
	b = append(b, frameReset)
	return binary.BigEndian.AppendUint32(b, code)
}

// readPreface reads HTTP/2's client preface.
func readPreface(c net.Conn) error {
	b := make([]byte, len(clientPreface))
	if err := readFull(c, b); err != nil {
		return err
	}
	if string(b) != clientPreface {
		return errMalformedFrame
	}
	return nil
}

// clientPreface is HTTP/2's client connection preface (http2.ClientPreface).
const clientPreface = "PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n"
