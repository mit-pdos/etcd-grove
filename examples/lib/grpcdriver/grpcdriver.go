// Package grpcdriver is the executable specification of what our proofs rely on from gRPC
// (grpc-go v1.84, as etcd's client and server and the QuePaxa kit use it), as a deployable server
// and client: each section below names one behavior the library guarantees, exercises it, and
// panics if it fails. Its top-level robustness theorem says the client never panics, in every
// execution over the net extension (cut, reset or delayed connections, refused dials), so each
// section asserts only what holds whatever the network does: properties of calls and stream
// operations that succeeded, and the shape of the errors otherwise.
//
// Two machines, each a process: the server (Server) serves the service svc.Driver at Addr; the
// client (Client) makes unary calls and streams of every kind, from random goroutines on one
// ClientConn, with random payloads, metadata and contexts. Every choice is the program's
// nondeterminism (primitive.RandomUint64): the theorem covers all of them. The behaviors and the
// call sites relying on them: notes/library-drivers.md.
package grpcdriver

import (
	"context"
	"errors"
	"io"
	"net"
	"strconv"
	"strings"
	"sync"

	"github.com/goose-lang/primitive"
	"github.com/mit-pdos/etcd-grove/examples/lib/grpcdriver/svc"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"
	"google.golang.org/protobuf/types/known/wrapperspb"
)

// Addr is the server's address.
const Addr = "127.0.0.1:7301"

// mdKey is the metadata key the client sets and the Meta method reads back.
const mdKey = "x-driver"

// Bounds on the client's random choices. They bound a test's run time; any finite values would do, but
// the proof's constants follow these (`ctrBudget = maxWorkers*maxOps + 1`, `wordOk`'s and `csUp`'s 16,
// `meta`'s at most 3 values), so a change here changes those constants.
const (
	maxWorkers = 4  // goroutines using the ClientConn concurrently
	maxOps     = 8  // operations per goroutine
	maxLen     = 16 // length of a payload, and of a stream (one message per payload byte)
	maxMD      = 3  // metadata values per call
)

// reached marks a section's check as reached; it does nothing (the tests count with it, to show
// that every section's property is checked on a real run: non-vacuity).
var reached = func(section string) {}

// below is a random number in [0, n) (0 if n is 0).
func below(n uint64) uint64 {
	if n == 0 {
		return 0
	}
	return primitive.RandomUint64() % n
}

// ---------------------------------------------------------------------------------------------
// The server.

// server implements svc.DriverServer.
type server struct {
	mu   sync.Mutex
	runs map[string]uint64
}

// Echo answers its request's value, with the number of runs on that value (counting this one).
func (s *server) Echo(ctx context.Context, m *svc.Msg) (*svc.Msg, error) {
	s.mu.Lock()
	s.runs[m.Value] = s.runs[m.Value] + 1
	n := s.runs[m.Value]
	s.mu.Unlock()
	return wrapperspb.String(m.Value + "#" + strconv.FormatUint(n, 10)), nil
}

// Fail fails with its request's value as the message: a status with code NotFound, or, for a
// value starting with 'p', a plain Go error.
func (s *server) Fail(ctx context.Context, m *svc.Msg) (*svc.Msg, error) {
	if strings.HasPrefix(m.Value, "p") {
		return nil, errors.New(m.Value)
	}
	return nil, status.Error(codes.NotFound, m.Value)
}

// Meta answers the values the call's metadata has at mdKey, joined by ",".
func (s *server) Meta(ctx context.Context, m *svc.Msg) (*svc.Msg, error) {
	md, ok := metadata.FromIncomingContext(ctx)
	if !ok {
		return wrapperspb.String(""), nil
	}
	return wrapperspb.String(strings.Join(md.Get(mdKey), ",")), nil
}

// ServerStream sends its request's value one byte per message, then ends the stream cleanly.
func (s *server) ServerStream(m *svc.Msg, st grpc.ServerStreamingServer[svc.Msg]) error {
	for i := 0; i < len(m.Value); i++ {
		if err := st.Send(wrapperspb.String(m.Value[i : i+1])); err != nil {
			return err
		}
	}
	return nil
}

// ClientStream answers the concatenation of the messages it received, once the client is done.
func (s *server) ClientStream(st grpc.ClientStreamingServer[svc.Msg, svc.Msg]) error {
	got := ""
	for {
		m, err := st.Recv()
		if err == io.EOF {
			return st.SendAndClose(wrapperspb.String(got))
		}
		if err != nil {
			return err
		}
		got = got + m.Value
	}
}

// Bidi sends back each message it receives, and ends cleanly once the client is done.
func (s *server) Bidi(st grpc.BidiStreamingServer[svc.Msg, svc.Msg]) error {
	for {
		m, err := st.Recv()
		if err == io.EOF {
			return nil
		}
		if err != nil {
			return err
		}
		if err := st.Send(m); err != nil {
			return err
		}
	}
}

// Server serves the service at Addr. It returns only if it cannot listen, or when Serve returns.
func Server() {
	s := grpc.NewServer()
	svc.RegisterDriverServer(s, &server{runs: make(map[string]uint64)})
	l, err := net.Listen("tcp", Addr)
	if err != nil {
		return
	}
	s.Serve(l)
}

// ---------------------------------------------------------------------------------------------
// The client.

// counter hands out the ids of the client's calls, unique within the client's run (from a random
// start, so that the runs of a test against one server rarely share ids).
type counter struct {
	mu   sync.Mutex
	next uint64
}

func (c *counter) take() uint64 {
	c.mu.Lock()
	id := c.next
	c.next = id + 1
	c.mu.Unlock()
	return id
}

// randomWord is a random string of letters of length at most maxLen.
func randomWord() string {
	n := below(maxLen + 1)
	b := make([]byte, n)
	for i := range b {
		b[i] = byte('a' + below(26))
	}
	return string(b)
}

// freshValue is a request value no other call of this run sends: the call's id, then random
// letters.
func freshValue(ids *counter) string {
	return "v" + strconv.FormatUint(ids.take(), 10) + randomWord()
}

// errOk is the shape every error of a call or stream operation has: a gRPC status (or, from a
// stream's Recv, io.EOF).
func errOk(err error) bool {
	if err == io.EOF {
		return true
	}
	_, ok := status.FromError(err)
	return ok
}

// checkErr is what the client relies on from any error.
func checkErr(err error) {
	// Section error-set: an error from gRPC is a status (status.FromError accepts it), or io.EOF.
	if !errOk(err) {
		panic("error-set: an error that is neither a status nor io.EOF")
	}
	reached("error-set")
}

// echo is the section unary-reply.
func echo(c svc.DriverClient, ids *counter) {
	// Section unary-reply: a unary call that returns no error ran the handler at most once on this
	// request (the value is fresh, so a second run would answer "#2"), and its reply is that run's.
	v := freshValue(ids)
	r, err := c.Echo(context.Background(), wrapperspb.String(v))
	if err != nil {
		checkErr(err)
		return
	}
	if r.Value != v+"#1" {
		panic("unary-reply: the reply is not the one run's answer to this request")
	}
	reached("unary-reply")
}

// fail is the section status-roundtrip.
func fail(c svc.DriverClient, ids *counter) {
	// Section status-roundtrip: a call whose handler failed returns an error. (gRPC also relays the
	// handler's error as a status carrying its message, with its code, or codes.Unknown for a plain
	// error; the proof does not state the code yet, an S3 gap (notes/library-drivers.md), so it is not
	// checked.)
	v := freshValue(ids)
	if below(2) == 0 {
		v = "p" + v
	}
	_, err := c.Fail(context.Background(), wrapperspb.String(v))
	if err == nil {
		panic("status-roundtrip: a call whose handler failed returned no error")
	}
	checkErr(err)
	reached("status-roundtrip")
}

// meta is the section metadata.
func meta(c svc.DriverClient) {
	// Section metadata: the values the caller's context carries at a key reach the handler, in
	// order.
	n := below(maxMD + 1)
	var vals []string
	ctx, cancel := context.WithCancel(context.Background())
	for i := uint64(0); i < n; i++ {
		v := randomWord()
		vals = append(vals, v)
		ctx = metadata.AppendToOutgoingContext(ctx, mdKey, v)
	}
	r, err := c.Meta(ctx, wrapperspb.String(""))
	cancel()
	if err != nil {
		checkErr(err)
		return
	}
	if r.Value != strings.Join(vals, ",") {
		panic("metadata: the handler saw other values than the caller sent")
	}
	reached("metadata")
}

// canceled is the section ctx-canceled.
func canceled(c svc.DriverClient, ids *counter) {
	// Section ctx-canceled: a call made with a context already cancelled fails with
	// codes.Canceled.
	ctx, cancel := context.WithCancel(context.Background())
	cancel()
	_, err := c.Echo(ctx, wrapperspb.String(freshValue(ids)))
	if status.Code(err) != codes.Canceled {
		panic("ctx-canceled: a call with a cancelled context did not fail with Canceled")
	}
	reached("ctx-canceled")
}

// serverStream is the section server-stream.
func serverStream(c svc.DriverClient) {
	// Section server-stream: the client receives the handler's messages in order, without loss
	// or duplication. (gRPC also ends the stream with io.EOF only after the handler returned
	// without error and every message was received, or before any message, grpc/grpc-go#9443;
	// the proof does not state that yet: an S3 gap, notes/library-drivers.md, so it is not checked.)
	v := randomWord()
	st, err := c.ServerStream(context.Background(), wrapperspb.String(v))
	if err != nil {
		checkErr(err)
		return
	}
	got := ""
	for {
		m, err := st.Recv()
		if err == io.EOF {
			reached("server-stream")
			return
		}
		if err != nil {
			checkErr(err)
			return
		}
		got = got + m.Value
		if !strings.HasPrefix(v, got) {
			panic("server-stream: a message out of order, lost or duplicated")
		}
	}
}

// clientStream is the section client-stream.
func clientStream(c svc.DriverClient) {
	// Section client-stream: once every Send succeeded, the handler's reply is to all of them,
	// in order.
	st, err := c.ClientStream(context.Background())
	if err != nil {
		checkErr(err)
		return
	}
	v := randomWord()
	for i := 0; i < len(v); i++ {
		if err := st.Send(wrapperspb.String(v[i : i+1])); err != nil {
			// A Send that fails may or may not have delivered its message (io.EOF: the stream
			// ended; its status is RecvMsg's).
			return
		}
	}
	r, err := st.CloseAndRecv()
	if err != nil {
		checkErr(err)
		return
	}
	if r.Value != v {
		panic("client-stream: the reply is not to the messages sent, in order")
	}
	reached("client-stream")
}

// bidi is the section bidi-stream.
func bidi(c svc.DriverClient) {
	// Section bidi-stream: each direction is a queue: the messages the client receives are those
	// the handler sent (here, back the client's own, in order). (io.EOF only after every message,
	// or before any, as in server-stream, is not checked: an S3 gap.)
	st, err := c.Bidi(context.Background())
	if err != nil {
		checkErr(err)
		return
	}
	v := randomWord()
	sent := ""
	for i := 0; i < len(v); i++ {
		err := st.Send(wrapperspb.String(v[i : i+1]))
		// A Send that fails may or may not have delivered its message: count it as sent.
		sent = sent + v[i:i+1]
		if err != nil {
			break
		}
	}
	// The echoes of what was sent, received before closing (the client still owns its sending end,
	// so what it sent is the whole up queue), then the close.
	got := ""
	for len(got) < len(sent) {
		m, err := st.Recv()
		if err == io.EOF {
			reached("bidi-stream")
			return
		}
		if err != nil {
			checkErr(err)
			return
		}
		got = got + m.Value
		if !strings.HasPrefix(sent, got) {
			panic("bidi-stream: a message out of order, lost, duplicated or never sent")
		}
	}
	st.CloseSend()
	reached("bidi-stream")
}

// work runs random operations on the ClientConn's client.
func work(c svc.DriverClient, ids *counter) {
	ops := below(maxOps + 1)
	for i := uint64(0); i < ops; i++ {
		switch below(7) {
		case 0:
			echo(c, ids)
		case 1:
			fail(c, ids)
		case 2:
			meta(c)
		case 3:
			canceled(c, ids)
		case 4:
			serverStream(c)
		case 5:
			clientStream(c)
		default:
			bidi(c)
		}
	}
}

// Client connects to the server and runs random operations from random goroutines on one
// ClientConn, then closes it.
func Client() {
	cc, err := grpc.NewClient("passthrough:///"+Addr,
		grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		return
	}
	c := svc.NewDriverClient(cc)
	ids := &counter{next: primitive.RandomUint64()}

	// Section concurrent-calls: unary calls and streams made concurrently on one ClientConn each
	// meet their own section's property.
	var wg sync.WaitGroup
	workers := 1 + below(maxWorkers)
	for w := uint64(0); w < workers; w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			work(c, ids)
		}()
	}
	wg.Wait()
	reached("concurrent-calls")

	// Section close: after the ClientConn is closed, a call fails with codes.Canceled.
	cc.Close()
	if _, err := c.Echo(context.Background(), wrapperspb.String(freshValue(ids))); status.Code(err) != codes.Canceled {
		panic("close: a call on a closed ClientConn did not fail with Canceled")
	}
	reached("close")
}
