package grpcdifftest_test

import (
	"context"
	"errors"
	"io"
	"net"
	"os"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/status"

	"dsverify.lab/grpcdifftest/arith"
	"dsverify.lab/grpcdifftest/codec"
	"dsverify.lab/grpcdifftest/pb"
)

// ids: fresh call ids, across -count runs.
var ids atomic.Uint64

func fresh() uint64 { return ids.Add(1) }

func TestMain(m *testing.M) {
	codec.Register()
	os.Exit(m.Run())
}

// serve starts a server for srv on a fresh loopback address.
func serve(t *testing.T, register func(*grpc.Server)) string {
	t.Helper()
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	s := grpc.NewServer()
	register(s)
	go s.Serve(l)
	t.Cleanup(func() { l.Close() })
	return l.Addr().String()
}

func serveArith(t *testing.T) (*arith.Server, string) {
	a := arith.New()
	return a, serve(t, func(s *grpc.Server) { pb.RegisterArithServer(s, a) })
}

func dial(t *testing.T, addr string) (*grpc.ClientConn, pb.ArithClient) {
	t.Helper()
	cc, err := grpc.NewClient(addr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { cc.Close() })
	return cc, pb.NewArithClient(cc)
}

func ctx5(t *testing.T) context.Context {
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	t.Cleanup(cancel)
	return ctx
}

// wantStatus checks err's code and (if msg != "") message, and its Error().
func wantStatus(t *testing.T, err error, c codes.Code, msg string) {
	t.Helper()
	if err == nil {
		t.Fatalf("got nil, want code %v", c)
	}
	s, ok := status.FromError(err)
	if !ok {
		t.Fatalf("not a status error: %v", err)
	}
	if s.Code() != c || status.Code(err) != c {
		t.Fatalf("code %v (%v), want %v", s.Code(), err, c)
	}
	if msg != "" {
		if s.Message() != msg {
			t.Fatalf("message %q, want %q", s.Message(), msg)
		}
		if err.Error() != "rpc error: code = "+c.String()+" desc = "+msg {
			t.Fatalf("Error() %q", err.Error())
		}
	}
}

// eventually waits up to 5 s for cond.
func eventually(t *testing.T, what string, cond func() bool) {
	t.Helper()
	for i := 0; i < 500; i++ {
		if cond() {
			return
		}
		time.Sleep(10 * time.Millisecond)
	}
	t.Fatalf("timed out waiting for %s", what)
}

func TestAdd(t *testing.T) {
	a, addr := serveArith(t)
	_, c := dial(t, addr)
	id := fresh()
	in := &pb.Args{A: 3, B: -5, Id: id, Op: pb.Op_SUB, Tag: "héllo", Blob: []byte{0, 1},
		Flag: true, Xs: []int64{1, -1}, Names: []string{"a", ""},
		Inner: &pb.Inner{K: "k", V: 7, Sub: &pb.Inner{}}, Inners: []*pb.Inner{{V: 1}, {}},
		Small: -3, Usmall: 4, Big: 9}
	r, err := c.Add(ctx5(t), in)
	if err != nil {
		t.Fatal(err)
	}
	if r.C != -2 || r.Echo.Tag != "héllo" || len(r.Echo.Inners) != 2 || r.Echo.Inner.Sub == nil ||
		r.Echo.Xs[1] != -1 || r.Echo.Big != 9 || r.Echo.Small != -3 {
		t.Fatalf("reply %v", r)
	}
	if a.Runs(id) != 1 {
		t.Fatalf("runs %d", a.Runs(id))
	}
}

func TestConcurrent(t *testing.T) {
	a, addr := serveArith(t)
	_, c := dial(t, addr)
	var wg sync.WaitGroup
	errs := make(chan error, 200)
	for i := 0; i < 200; i++ {
		wg.Add(1)
		go func(i int64) {
			defer wg.Done()
			id := fresh()
			r, err := c.Add(context.Background(), &pb.Args{A: i, B: i, Id: id})
			if err != nil || r.C != 2*i || a.Runs(id) != 1 {
				errs <- errors.New("bad concurrent call")
			}
		}(int64(i))
	}
	wg.Wait()
	close(errs)
	for err := range errs {
		t.Fatal(err)
	}
}

func TestHandlerErrors(t *testing.T) {
	a, addr := serveArith(t)
	_, c := dial(t, addr)
	id := fresh()
	_, err := c.Div(ctx5(t), &pb.Args{A: 1, B: 0, Id: id})
	wantStatus(t, err, codes.InvalidArgument, "division by zero")
	_, err = c.Div(ctx5(t), &pb.Args{A: 1, B: 1, Tag: "plain", Id: id})
	wantStatus(t, err, codes.Unknown, "plain failure")
	_, err = c.Div(ctx5(t), &pb.Args{A: 1, B: 1, Tag: "deadline", Id: id})
	wantStatus(t, err, codes.DeadlineExceeded, "context deadline exceeded")
	r, err := c.Div(ctx5(t), &pb.Args{A: 1, B: 1, Tag: "typednil", Id: id})
	if err != nil || r.C != 0 || r.Echo != nil {
		t.Fatalf("typed nil reply: %v %v", r, err)
	}
	if a.Runs(id) != 4 {
		t.Fatalf("runs %d", a.Runs(id))
	}
}

// rawDesc is a service whose handler returns a nil reply (no generated code does): the real
// encode sends the empty message.
var rawDesc = grpc.ServiceDesc{
	ServiceName: "raw.Raw",
	HandlerType: (*interface{})(nil),
	Methods: []grpc.MethodDesc{{
		MethodName: "Nil",
		Handler: func(srv interface{}, ctx context.Context, dec func(interface{}) error, _ grpc.UnaryServerInterceptor) (interface{}, error) {
			in := new(pb.Empty)
			if err := dec(in); err != nil {
				return nil, err
			}
			return nil, nil
		},
	}},
	Streams: []grpc.StreamDesc{},
}

func TestNilReply(t *testing.T) {
	addr := serve(t, func(s *grpc.Server) { s.RegisterService(&rawDesc, struct{}{}) })
	cc, _ := dial(t, addr)
	if err := cc.Invoke(ctx5(t), "/raw.Raw/Nil", &pb.Empty{}, new(pb.Empty)); err != nil {
		t.Fatal(err)
	}
	// a nil request is the empty message too
	if err := cc.Invoke(ctx5(t), "/raw.Raw/Nil", nil, new(pb.Empty)); err != nil {
		t.Fatal(err)
	}
}

func TestUnknownMethod(t *testing.T) {
	_, addr := serveArith(t)
	cc, _ := dial(t, addr)
	err := cc.Invoke(ctx5(t), "/arith.Arith/Mul", &pb.Args{}, new(pb.Reply))
	wantStatus(t, err, codes.Unimplemented, "unknown method Mul for service arith.Arith")
	err = cc.Invoke(ctx5(t), "/nope.Nope/Add", &pb.Args{}, new(pb.Reply))
	wantStatus(t, err, codes.Unimplemented, "unknown service nope.Nope")
	err = cc.Invoke(ctx5(t), "/noslash", &pb.Args{}, new(pb.Reply))
	wantStatus(t, err, codes.Unimplemented, "")
}

type unimpl struct{ pb.UnimplementedArithServer }

func TestUnimplementedServer(t *testing.T) {
	addr := serve(t, func(s *grpc.Server) { pb.RegisterArithServer(s, unimpl{}) })
	_, c := dial(t, addr)
	_, err := c.Add(ctx5(t), &pb.Args{})
	wantStatus(t, err, codes.Unimplemented, "method Add not implemented")
}

func TestDeadline(t *testing.T) {
	a, addr := serveArith(t)
	_, c := dial(t, addr)
	id := fresh()
	ctx, cancel := context.WithTimeout(context.Background(), 200*time.Millisecond)
	defer cancel()
	_, err := c.Div(ctx, &pb.Args{A: 1, B: 1, Tag: "wait", Id: id})
	wantStatus(t, err, codes.DeadlineExceeded, "context deadline exceeded")
	eventually(t, "the handler's context to be done", func() bool { return a.CtxDone(id) })
	if a.Runs(id) != 1 {
		t.Fatalf("runs %d", a.Runs(id))
	}
	// the connection is still usable
	if _, err := c.Add(ctx5(t), &pb.Args{A: 1}); err != nil {
		t.Fatal(err)
	}
}

func TestCancel(t *testing.T) {
	a, addr := serveArith(t)
	_, c := dial(t, addr)
	id := fresh()
	ctx, cancel := context.WithCancel(context.Background())
	go func() {
		eventually(t, "the handler to run", func() bool { return a.Runs(id) == 1 })
		cancel()
	}()
	_, err := c.Div(ctx, &pb.Args{A: 1, B: 1, Tag: "wait", Id: id})
	wantStatus(t, err, codes.Canceled, "context canceled")
	eventually(t, "the handler's context to be done", func() bool { return a.CtxDone(id) })
}

func TestCanceledBefore(t *testing.T) {
	a, addr := serveArith(t)
	_, c := dial(t, addr)
	id := fresh()
	ctx, cancel := context.WithCancel(context.Background())
	cancel()
	_, err := c.Add(ctx, &pb.Args{Id: id})
	wantStatus(t, err, codes.Canceled, "context canceled")
	time.Sleep(50 * time.Millisecond)
	if a.Runs(id) != 0 {
		t.Fatalf("runs %d", a.Runs(id))
	}
}

func TestReleased(t *testing.T) {
	a, addr := serveArith(t)
	_, c := dial(t, addr)
	id := fresh()
	go func() {
		eventually(t, "the handler to run", func() bool { return a.Runs(id) == 1 })
		a.Release(id)
	}()
	r, err := c.Div(ctx5(t), &pb.Args{A: 6, B: 3, Tag: "wait", Id: id})
	if err != nil || r.C != 2 {
		t.Fatal(r, err)
	}
}

func TestNoCredentials(t *testing.T) {
	cc, err := grpc.NewClient("127.0.0.1:1")
	if err == nil || cc != nil {
		t.Fatalf("NewClient without credentials: %v %v", cc, err)
	}
	cc, err = grpc.Dial("127.0.0.1:1")
	if err == nil || cc != nil {
		t.Fatalf("Dial without credentials: %v %v", cc, err)
	}
}

func freeAddr(t *testing.T) string {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	a := l.Addr().String()
	l.Close()
	return a
}

func TestUnavailable(t *testing.T) {
	addr := freeAddr(t)
	cc, err := grpc.Dial(addr, grpc.WithInsecure())
	if err != nil {
		t.Fatal(err)
	}
	defer cc.Close()
	err = cc.Invoke(ctx5(t), "/arith.Arith/Add", &pb.Args{}, new(pb.Reply))
	wantStatus(t, err, codes.Unavailable, "")
}

// proxy forwards connections on its own address to target, until cut closes them all.
type proxy struct {
	l      net.Listener
	mu     sync.Mutex
	conns  []net.Conn
	target string
}

func newProxy(t *testing.T, target string) *proxy {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	p := &proxy{l: l, target: target}
	t.Cleanup(func() { l.Close(); p.cut() })
	go func() {
		for {
			c, err := l.Accept()
			if err != nil {
				return
			}
			s, err := net.Dial("tcp", target)
			if err != nil {
				c.Close()
				continue
			}
			p.mu.Lock()
			p.conns = append(p.conns, c, s)
			p.mu.Unlock()
			go func() { io.Copy(s, c); s.Close() }()
			go func() { io.Copy(c, s); c.Close() }()
		}
	}()
	return p
}

func (p *proxy) cut() {
	p.mu.Lock()
	for _, c := range p.conns {
		c.Close()
	}
	p.conns = nil
	p.mu.Unlock()
}

// TestReconnect: after the connection breaks, a later call succeeds over a new connection; no
// handler runs twice for one call.
func TestReconnect(t *testing.T) {
	a, addr := serveArith(t)
	p := newProxy(t, addr)
	_, c := dial(t, p.l.Addr().String())
	if _, err := c.Add(ctx5(t), &pb.Args{A: 1, Id: fresh()}); err != nil {
		t.Fatal(err)
	}
	p.cut()
	ok := false
	for i := 0; i < 300 && !ok; i++ {
		id := fresh()
		_, err := c.Add(ctx5(t), &pb.Args{A: 1, Id: id})
		if a.Runs(id) > 1 {
			t.Fatalf("runs %d", a.Runs(id))
		}
		if err == nil {
			ok = true
		} else {
			if s := status.Code(err); s != codes.Unavailable {
				t.Fatalf("after a cut: %v", err)
			}
			time.Sleep(20 * time.Millisecond)
		}
	}
	if !ok {
		t.Fatal("no call succeeded after the cut")
	}
}

// TestCutWhileWaiting: a call pending when the connection breaks fails with Unavailable, after
// its handler ran once.
func TestCutWhileWaiting(t *testing.T) {
	a, addr := serveArith(t)
	p := newProxy(t, addr)
	_, c := dial(t, p.l.Addr().String())
	id := fresh()
	go func() {
		eventually(t, "the handler to run", func() bool { return a.Runs(id) == 1 })
		p.cut()
	}()
	_, err := c.Div(ctx5(t), &pb.Args{A: 1, B: 1, Tag: "wait", Id: id})
	wantStatus(t, err, codes.Unavailable, "")
	eventually(t, "the handler's context to be done", func() bool { return a.CtxDone(id) })
}

func TestBigMessages(t *testing.T) {
	a, addr := serveArith(t)
	_, c := dial(t, addr)
	id := fresh()
	_, err := c.Add(ctx5(t), &pb.Args{Id: id, Blob: make([]byte, 4*1024*1024+1)})
	wantStatus(t, err, codes.ResourceExhausted, "")
	if a.Runs(id) != 0 {
		t.Fatalf("runs %d", a.Runs(id))
	}
	id = fresh()
	_, err = c.Div(ctx5(t), &pb.Args{Id: id, Tag: "big", B: 1})
	wantStatus(t, err, codes.ResourceExhausted, "")
	if a.Runs(id) != 1 {
		t.Fatalf("runs %d", a.Runs(id))
	}
	// just under the limit
	_, err = c.Add(ctx5(t), &pb.Args{Blob: make([]byte, 4*1024*1024-64)})
	if err != nil {
		t.Fatal(err)
	}
}

func TestClose(t *testing.T) {
	_, addr := serveArith(t)
	cc, err := grpc.NewClient(addr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	c := pb.NewArithClient(cc)
	if _, err := c.Add(ctx5(t), &pb.Args{}); err != nil {
		t.Fatal(err)
	}
	if err := cc.Close(); err != nil {
		t.Fatal(err)
	}
	_, err = c.Add(ctx5(t), &pb.Args{})
	wantStatus(t, err, codes.Canceled, "")
	if err := cc.Close(); err == nil || status.Code(err) != codes.Canceled {
		t.Fatalf("second Close: %v", err)
	}
}

func TestServeReturns(t *testing.T) {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	s := grpc.NewServer()
	pb.RegisterArithServer(s, arith.New())
	done := make(chan error, 1)
	go func() { done <- s.Serve(l) }()
	time.Sleep(50 * time.Millisecond)
	l.Close()
	select {
	case err := <-done:
		if err == nil {
			t.Fatal("Serve returned nil")
		}
	case <-time.After(5 * time.Second):
		t.Fatal("Serve did not return")
	}
}

func TestStatusPackage(t *testing.T) {
	if status.New(codes.OK, "x").Err() != nil || status.Error(codes.OK, "x") != nil {
		t.Fatal("OK is not nil")
	}
	s, ok := status.FromError(nil)
	if s != nil || !ok || s.Code() != codes.OK || s.Message() != "" || status.Code(nil) != codes.OK {
		t.Fatal("FromError(nil)")
	}
	s, ok = status.FromError(errors.New("x"))
	if ok || s.Code() != codes.Unknown || s.Message() != "x" || status.Code(errors.New("x")) != codes.Unknown {
		t.Fatal("FromError(plain)")
	}
	if status.Convert(errors.New("y")).Message() != "y" {
		t.Fatal("Convert")
	}
	e := status.Errorf(codes.NotFound, "n %d %s", 3, "z")
	if e.Error() != "rpc error: code = NotFound desc = n 3 z" {
		t.Fatalf("Errorf: %q", e.Error())
	}
	if status.Newf(codes.Aborted, "a%d", 1).Message() != "a1" {
		t.Fatal("Newf")
	}
	for c := codes.Code(0); c < 20; c++ {
		want := map[codes.Code]string{0: "OK", 1: "Canceled", 2: "Unknown", 3: "InvalidArgument",
			4: "DeadlineExceeded", 5: "NotFound", 6: "AlreadyExists", 7: "PermissionDenied",
			8: "ResourceExhausted", 9: "FailedPrecondition", 10: "Aborted", 11: "OutOfRange",
			12: "Unimplemented", 13: "Internal", 14: "Unavailable", 15: "DataLoss",
			16: "Unauthenticated"}[c]
		if want == "" {
			want = "Code(" + strings.TrimLeft(string(rune('0'+c/10))+string(rune('0'+c%10)), "0") + ")"
		}
		if c.String() != want {
			t.Fatalf("%d: %q want %q", c, c.String(), want)
		}
	}
	if status.FromContextError(context.Canceled).Code() != codes.Canceled ||
		status.FromContextError(context.DeadlineExceeded).Code() != codes.DeadlineExceeded ||
		status.FromContextError(errors.New("q")).Code() != codes.Unknown ||
		status.FromContextError(nil) != nil {
		t.Fatal("FromContextError")
	}
	_ = model
}
