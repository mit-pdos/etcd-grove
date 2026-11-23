// MODEL: this file is the model's own (not in Go's net/rpc).
//
// Package rpc here is a model of Go 1.27.3's net/rpc (models/README.md): Go's code, but for the
// parts reflection and gob do, which this file replaces. Every exported name of Go's package is
// kept, with Go's code wherever it does not use reflection or gob (the Client and its pending
// calls, Go, Call, Close, Dial, DialHTTP, DialHTTPPath; the Server's request loop, ServeCodec,
// ServeRequest, Accept, ServeHTTP, HandleHTTP; Register's checks and messages); the places
// changed are marked MODEL.
//
// The claim (trusted): every behavior of Go's net/rpc, as the program observes it, is a behavior
// of this model, when every peer of the program also runs it (the wire format is the model's
// own, not gob's: see below). Where the model does not model Go's behavior it panics ("net/rpc
// model: ..."), so that a proof that the program does not panic shows it never gets there.
//
// What replaces reflection and gob is a Codec, which the program registers (SetCodec), generated
// for the program's types and receivers by models/net/rpc/rpcgen.py (the trusted generator; its
// core rpcgen_core.py says, per type, what is gob's behavior it reproduces):
//   - Encode and Decode: gob's Encode, and its Decode into a value (merging into the value's
//     fields as gob does), for the types the generator accepted; a value of an unlisted type, a
//     nil value, or decoding a value of one type into another type panics (gob's decoding across
//     types, matching struct fields by name, is not modelled);
//   - Receiver: what reflection tells Register about a receiver (its type's name and string, the
//     methods suitableMethods registers, whether a pointer to it would have some), and per method
//     the values readRequest makes (reflect.New) and the call (reflect.Value.Call).
//
// The wire (the model's own; gob's encoding of the same values differs): each gob message (a
// request or response header, a body) is a frame, its length in 8 bytes (little-endian) and its
// payload. A header frame holds the sequence number, the service method and, in a response, the
// error string; a body frame holds the Codec's encoding of the value (empty after an error
// response: the client discards it, as it discards gob's placeholder). The read errors are gob's:
// io.EOF if the connection ends before a frame, io.ErrUnexpectedEOF if within one (gob's two
// cases), the connection's error otherwise; a frame longer than maxFrame, or a header frame that
// does not parse, is an error the model's own (gob's malformed input errors are not modelled:
// no model peer sends such input). Write errors are sticky, as gob's bufio.Writer's. The server
// codec's frame read errors are sticky too (serverCodec.rerr): after one, every later read fails
// with it. Go's gob reads on after a read error; the server loop then reads on only after a body's
// read error (ServeCodec answers it and continues), and a frame cut short leaves gob, and the
// model, in the middle of a frame, reading from there as if a frame started. Over Linux a
// connection's end yields no byte after a read error (an error comes once the unread bytes are
// read: then EOF, examples/net/semantics' TestResetInNetwork, TestKilledWithUnreadInput,
// TestTimeoutOnBreak), so Go's later reads fail too and the loop ends at the next header, as the
// model's does: the same behavior, but for a read deadline's timeout, after which Go reads on
// (outside the model's claim: a program that sets a read deadline on a connection it serves; the
// net extension's semantics allows bytes after a read error too, which is why the model says it).
package rpc

import (
	"errors"
	"io"
	"sync"
)

// A Method is what the model knows of one method that reflection's suitableMethods registers.
type Method struct {
	// NewArg returns a pointer to a new zero value of the method's argument type (if the
	// argument type is a pointer, its element type: Go's reflect.New in readRequest).
	NewArg func() any
	// NewReply returns a pointer to a new zero value of the reply's element type, holding an
	// empty map or slice if it is one (Go's reflect.New, reflect.MakeMap, reflect.MakeSlice).
	NewReply func() any
	// Call calls the method of rcvr with argv (NewArg's pointer, dereferenced if the method
	// takes a value) and replyv (NewReply's) and returns its error (Go's reflect.Value.Call).
	Call func(rcvr, argv, replyv any) error
}

// A Receiver is what reflection tells Register about a receiver value.
type Receiver struct {
	// Name is the name of the receiver's type, through a pointer (reflect.Indirect's).
	Name string
	// NilPtr: the receiver is a nil pointer (reflect.Indirect's Type panics on it).
	NilPtr bool
	// Type is the receiver's type's String (reflect.TypeOf's).
	Type string
	// Methods are the methods suitableMethods registers for the receiver's type.
	Methods map[string]*Method
	// PtrHasMethods: suitableMethods registers some method for a pointer to the type.
	PtrHasMethods bool
}

// A Codec stands in for gob and reflection, generated for a program's types by rpcgen.py.
type Codec struct {
	// Encode is gob's encoding of v (a value of a listed type, or a non-nil pointer to one).
	Encode func(v any) []byte
	// Decode decodes data (Encode's) into *ptr as gob does (ptr: a non-nil pointer to a value of
	// a listed type, of data's type).
	Decode func(data []byte, ptr any) error
	// Receiver is reflection's view of a receiver of a listed type.
	Receiver func(rcvr any) *Receiver
}

// notModelled is the value the model panics with where it does not model Go's behavior (the
// net/http model's server panics again with a value that has a NotModelled method, instead of
// recovering it as a handler's panic).
type notModelled string

// NotModelled marks the value as the models' panic.
func (notModelled) NotModelled() {}

var codecMu sync.Mutex
var codec *Codec

// SetCodec registers the program's codec (generated by rpcgen.py). A second registration
// panics: a program has one codec, for all its types.
func SetCodec(c *Codec) {
	codecMu.Lock()
	if codec != nil {
		codecMu.Unlock()
		panic(notModelled("net/rpc model: a second codec registered"))
	}
	codec = c
	codecMu.Unlock()
}

func getCodec() *Codec {
	codecMu.Lock()
	c := codec
	codecMu.Unlock()
	if c == nil {
		panic(notModelled("net/rpc model: no codec registered (the program's generated codec registers it)"))
	}
	return c
}

// maxFrame bounds a frame's length (gob's tooBig, 1 GiB on 64-bit machines, is larger; a longer
// frame is an error).
const maxFrame uint64 = 1 << 30

var errFrame = errors.New("rpc: malformed frame")

func putU64(b []byte, x uint64) []byte {
	return append(b, byte(x), byte(x>>8), byte(x>>16), byte(x>>24), byte(x>>32), byte(x>>40),
		byte(x>>48), byte(x>>56))
}

func getU64(b []byte) uint64 {
	return uint64(b[0]) | uint64(b[1])<<8 | uint64(b[2])<<16 | uint64(b[3])<<24 |
		uint64(b[4])<<32 | uint64(b[5])<<40 | uint64(b[6])<<48 | uint64(b[7])<<56
}

func putString(b []byte, s string) []byte {
	b = putU64(b, uint64(len(s)))
	return append(b, s...)
}

// putFrame appends a frame holding payload.
func putFrame(b []byte, payload []byte) []byte {
	b = putU64(b, uint64(len(payload)))
	return append(b, payload...)
}

// readFull reads len(b) bytes of a frame from r: io.EOF if r ends before the first byte of the
// frame (first), io.ErrUnexpectedEOF if after it, r's error otherwise (gob's recvMessage).
func readFull(r io.Reader, b []byte, first bool) error {
	n := 0
	for n < len(b) {
		k, err := r.Read(b[n:])
		n = n + k
		if n == len(b) {
			return nil
		}
		if err != nil {
			if err == io.EOF && (n > 0 || !first) {
				return io.ErrUnexpectedEOF
			}
			return err
		}
	}
	return nil
}

// readFrame reads one frame and returns its payload.
func readFrame(r io.Reader) ([]byte, error) {
	h := make([]byte, 8)
	if err := readFull(r, h, true); err != nil {
		return nil, err
	}
	n := getU64(h)
	if n > maxFrame {
		return nil, errFrame
	}
	p := make([]byte, n)
	if err := readFull(r, p, false); err != nil {
		return nil, err
	}
	return p, nil
}

// getString reads a string (its length, then its bytes) off p.
func getString(p []byte) (string, []byte, bool) {
	if len(p) < 8 {
		return "", nil, false
	}
	n := getU64(p)
	if n > uint64(len(p)-8) {
		return "", nil, false
	}
	return string(p[8 : 8+n]), p[8+n:], true
}

// clientCodec is the model's ClientCodec (gob's gobClientCodec in Go).
type clientCodec struct {
	rwc  io.ReadWriteCloser
	werr error // the first write error: every later write fails with it (gob's bufio.Writer)
}

func newClientCodec(conn io.ReadWriteCloser) *clientCodec {
	return &clientCodec{rwc: conn}
}

func (c *clientCodec) WriteRequest(r *Request, body any) error {
	if c.werr != nil {
		return c.werr
	}
	h := putU64(nil, r.Seq)
	h = putString(h, r.ServiceMethod)
	b := putFrame(nil, h)
	b = putFrame(b, getCodec().Encode(body))
	if _, err := c.rwc.Write(b); err != nil {
		c.werr = err
		return err
	}
	return nil
}

func (c *clientCodec) ReadResponseHeader(r *Response) error {
	p, err := readFrame(c.rwc)
	if err != nil {
		return err
	}
	if len(p) < 8 {
		return errFrame
	}
	seq := getU64(p)
	sm, rest, ok := getString(p[8:])
	if !ok {
		return errFrame
	}
	e, rest2, ok2 := getString(rest)
	if !ok2 || len(rest2) != 0 {
		return errFrame
	}
	r.ServiceMethod = sm
	r.Seq = seq
	r.Error = e
	return nil
}

// ReadResponseBody reads the body frame that follows the header (with body nil, to discard it).
func (c *clientCodec) ReadResponseBody(body any) error {
	p, err := readFrame(c.rwc)
	if err != nil {
		return err
	}
	if body == nil {
		return nil
	}
	return getCodec().Decode(p, body)
}

func (c *clientCodec) Close() error {
	return c.rwc.Close()
}

// serverCodec is the model's ServerCodec (gob's gobServerCodec in Go).
type serverCodec struct {
	rwc    io.ReadWriteCloser
	werr   error // as clientCodec's
	rerr   error // the first frame read error: every later read fails with it (the package doc)
	closed bool
}

func newServerCodec(conn io.ReadWriteCloser) *serverCodec {
	return &serverCodec{rwc: conn}
}

func (c *serverCodec) ReadRequestHeader(r *Request) error {
	if c.rerr != nil {
		return c.rerr
	}
	p, err := readFrame(c.rwc)
	if err != nil {
		c.rerr = err
		return err
	}
	if len(p) < 8 {
		return errFrame
	}
	seq := getU64(p)
	sm, rest, ok := getString(p[8:])
	if !ok || len(rest) != 0 {
		return errFrame
	}
	r.ServiceMethod = sm
	r.Seq = seq
	return nil
}

// ReadRequestBody reads the body frame that follows the header (with body nil, to discard it).
func (c *serverCodec) ReadRequestBody(body any) error {
	if c.rerr != nil {
		return c.rerr
	}
	p, err := readFrame(c.rwc)
	if err != nil {
		c.rerr = err
		return err
	}
	if body == nil {
		return nil
	}
	return getCodec().Decode(p, body)
}

// WriteResponse writes the header and, unless it is an error response, the body's encoding
// (after an error, Go sends a placeholder the client discards unread; the model sends an empty
// body frame).
func (c *serverCodec) WriteResponse(r *Response, body any) error {
	if c.werr != nil {
		return c.werr
	}
	h := putU64(nil, r.Seq)
	h = putString(h, r.ServiceMethod)
	h = putString(h, r.Error)
	b := putFrame(nil, h)
	if r.Error == "" {
		b = putFrame(b, getCodec().Encode(body))
	} else {
		b = putFrame(b, nil)
	}
	if _, err := c.rwc.Write(b); err != nil {
		c.werr = err
		return err
	}
	return nil
}

func (c *serverCodec) Close() error {
	if c.closed {
		// Only call c.rwc.Close once; otherwise the semantics are undefined.
		return nil
	}
	c.closed = true
	return c.rwc.Close()
}
