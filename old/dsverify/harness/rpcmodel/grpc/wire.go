// Package grpc is the dsverify lab's model of google.golang.org/grpc (v1.84.0), the unary subset
// (notes/grpc-model.md). It is plain Go over net.Conn; Goose translates it in place of the real
// module (a kit's model-mode modfile replaces the module by this directory) and the harness
// proves its specs once over the net model (harness/lean/Harness/Proof/grpc).
//
// The subset: Dial, DialContext, NewClient with WithInsecure or
// WithTransportCredentials(insecure.NewCredentials()) (and WithBlock ignored);
// (*ClientConn).Invoke, Close; ClientConnInterface; CallOption values (ignored); NewServer,
// (*Server).RegisterService, Serve; ServiceDesc, MethodDesc, MethodHandler, the unary
// interceptor types the generated code names; packages codes, status, credentials/insecure.
// Streams, interceptors, server options, Stop and GracefulStop are not modeled (no such names, or
// a call panics), so code that uses them does not build or is stuck: outside the subset.
//
// The wire format is the model's own (every node of a theorem runs the model; it is not HTTP/2):
// on a TCP connection, length-prefixed frames (8 bytes little-endian, then the payload); a
// payload is encodeMsg(tag, seq, s, body): from the client, a call (tag 0, the call's sequence
// number, the full method name "/service/method", the encoded request) or a cancellation (tag 1,
// the sequence number of the call the client gave up); from the server, an answer (tag the status
// code, the sequence number, the status message, the encoded reply). A call's sequence number is
// the number of its frame among the client's frames on the connection (from 0).
//
// Semantics, the trusted claim (tested against the real module by harness/rpcmodel/grpcdifftest
// and a kit's tests run in both modes): Invoke returns nil after the server ran the method's
// handler once on the decoded request, with the handler's reply decoded into reply; or a status
// error, in which case the handler ran at most once (the real module never runs a unary handler
// twice for one Invoke: its transparent retry resends only a request no server handler received,
// and retry policies are off without a service config). The status codes: the handler's status
// (Unknown for an error that is not a status, DeadlineExceeded/Canceled for the context errors),
// Unimplemented for an unknown service or method, Internal for a request or reply the codec cannot
// encode or decode, ResourceExhausted for a message over the default limits (4 MiB received,
// 2^31-1 sent), Unavailable for a broken or refused connection, DeadlineExceeded or Canceled when
// the call's context is done (at any point: time is not modeled, so a deadline may expire at any
// moment, as the net model's deadlines), Canceled after Close. Only the codes are claimed, and the
// messages of the handler's statuses, the unknown-method errors and the context errors; other
// messages are the model's.
//
// A ClientConn connects lazily, at its first call, and again at the next call after its
// connection broke (as the real one reconnects; the model has no backoff, so it may dial again at
// once, which a real one does after its backoff). Calls on one ClientConn may be concurrent (a
// sequence number per call, a pending map, a reader goroutine per connection, as net/rpc's
// model). A server runs each call's handler in its own goroutine, with a context that is canceled
// when the handler returns, when the client gives the call up (its cancellation frame) and when
// the connection ends (as the real server's stream context).
package grpc

import (
	"errors"
	"net"
)

// maxFrame bounds a frame's length (a longer length prefix is a protocol error): above any
// payload the model writes (messages are limited to 2^31-1 bytes, as the real default send
// limit).
const maxFrame uint64 = 1 << 32

// maxRecvMsgSize and maxSendMsgSize are the real defaults (defaultServerMaxReceiveMessageSize,
// defaultClientMaxReceiveMessageSize, defaultServerMaxSendMessageSize,
// defaultClientMaxSendMessageSize: 4 MiB and math.MaxInt32).
const maxRecvMsgSize uint64 = 4 * 1024 * 1024
const maxSendMsgSize uint64 = 2147483647

// maxSeq: a transport writes at most maxSeq frames (their numbers are 0 to maxSeq-1).
const maxSeq uint64 = 18446744073709551615

// The tags of the client's payloads.
const tagCall uint64 = 0
const tagCancel uint64 = 1

var errFrame = errors.New("grpc: malformed frame")

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

// encodeMsg is a payload: the tag, the sequence number, the string's length and bytes, the body.
func encodeMsg(tag uint64, seq uint64, s string, body []byte) []byte {
	sb := []byte(s)
	b := make([]byte, 0, 24+uint64(len(sb))+uint64(len(body)))
	b = putU64(b, tag)
	b = putU64(b, seq)
	b = putU64(b, uint64(len(sb)))
	b = append(b, sb...)
	b = append(b, body...)
	return b
}

// decodeMsg parses encodeMsg's payload: (tag, seq, s, body, true), or false if malformed.
func decodeMsg(p []byte) (uint64, uint64, string, []byte, bool) {
	if uint64(len(p)) < 24 {
		return 0, 0, "", nil, false
	}
	tag := getU64(p[0:8])
	seq := getU64(p[8:16])
	n := getU64(p[16:24])
	if n > uint64(len(p))-24 {
		return 0, 0, "", nil, false
	}
	s := string(p[24 : 24+n])
	return tag, seq, s, p[24+n:], true
}
