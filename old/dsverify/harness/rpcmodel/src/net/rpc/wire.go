// Package rpc is the dsverify lab's model of Go's net/rpc (Go 1.27.3), for targets that use it
// (notes/craq-net.md decision 1). It is plain Go over net.Conn; Goose translates it in place of
// the real package (harness/rpcmodel/goroot.sh builds the GOROOT that substitutes it), and the
// harness proves its specs once over the net model (harness/lean/Harness/Proof/net/rpc and
// net/http; notes/craq-net.md, "rpc specs").
//
// The subset (what go-craq and SwiftPaxos use): DialHTTP, DialHTTPPath, (*Client).Call,
// (*Client).Close, ServerError, ErrShutdown; Register, RegisterName, HandleHTTP, NewServer,
// (*Server).Register, (*Server).RegisterName, (*Server).HandleHTTP, (*Server).ServeHTTP,
// (*Server).ServeConn, DefaultServer, DefaultRPCPath, DefaultDebugPath. Every node of a theorem runs the model, so the wire format
// is the model's own (length-prefixed frames; the HTTP CONNECT handshake's bytes as Go's).
//
// gob and reflection are replaced by a Codec (codec.go) that the kit's generated code registers
// (harness/kitgen, kit.toml's [rpc]): encoders, decoders and the dispatch table for exactly the
// kit's listed types and methods. A value of an unlisted type, a receiver of an unlisted type, or
// a nil pointer argument makes the model panic: outside the subset, never a silent error.
//
// Semantics (the trusted claim, tested against the real package by harness/rpcmodel/difftest and
// the kits' tests run in both modes): Call returns nil after the server ran the method once on a
// copy of the arguments, with the reply decoded into the caller's reply value; or a non-nil
// error, in which case the method ran at most once. Calls on one client may be concurrent (a
// sequence number per call, a pending map, a reader goroutine); a server runs each request in its
// own goroutine. After a connection error every pending and later Call returns an error.
package rpc

import (
	"errors"
	"net"
)

// maxFrame bounds a frame's length (a longer length prefix is a protocol error).
const maxFrame uint64 = 1 << 26

var errFrame = errors.New("rpc: malformed frame")

func putU64(b []byte, x uint64) []byte {
	return append(b, byte(x), byte(x>>8), byte(x>>16), byte(x>>24), byte(x>>32), byte(x>>40),
		byte(x>>48), byte(x>>56))
}

func getU64(b []byte) uint64 {
	return uint64(b[0]) | uint64(b[1])<<8 | uint64(b[2])<<16 | uint64(b[3])<<24 |
		uint64(b[4])<<32 | uint64(b[5])<<40 | uint64(b[6])<<48 | uint64(b[7])<<56
}

// readFull reads exactly n bytes from c, or fails.
func readFull(c net.Conn, n uint64) ([]byte, error) {
	b := make([]byte, n)
	var off uint64 = 0
	for off < n {
		k, err := c.Read(b[off:])
		if err != nil {
			return nil, err
		}
		off = off + uint64(k)
	}
	return b, nil
}

// writeFrame writes the length of payload (8 bytes, little-endian) and payload.
func writeFrame(c net.Conn, payload []byte) error {
	b := make([]byte, 0, 8+uint64(len(payload)))
	b = putU64(b, uint64(len(payload)))
	b = append(b, payload...)
	_, err := c.Write(b)
	return err
}

// readFrame reads one frame written by writeFrame and returns its payload.
func readFrame(c net.Conn) ([]byte, error) {
	h, err := readFull(c, 8)
	if err != nil {
		return nil, err
	}
	n := getU64(h)
	if n > maxFrame {
		return nil, errFrame
	}
	return readFull(c, n)
}

// encodeMsg is a request (seq, "Service.Method", the encoded argument) or a response (seq, the
// error message, "" for none, the encoded reply).
func encodeMsg(seq uint64, s string, body []byte) []byte {
	sb := []byte(s)
	b := make([]byte, 0, 16+uint64(len(sb))+uint64(len(body)))
	b = putU64(b, seq)
	b = putU64(b, uint64(len(sb)))
	b = append(b, sb...)
	b = append(b, body...)
	return b
}

func decodeMsg(p []byte) (uint64, string, []byte, bool) {
	if uint64(len(p)) < 16 {
		return 0, "", nil, false
	}
	seq := getU64(p[0:8])
	n := getU64(p[8:16])
	if n > uint64(len(p))-16 {
		return 0, "", nil, false
	}
	s := string(p[16 : 16+n])
	return seq, s, p[16+n:], true
}
