// The grpc model's differential test: every test runs, unchanged, against the real grpc-go
// v1.84.0 (this module's go.mod) and against the model (models/grpc, substituted by
// models/grpc/gomodel.py; run.sh runs both). A test checks what a program observes: what calls
// and streams return (codes, messages, replies, metadata, peers), what handlers see (requests,
// metadata, deadlines, contexts canceled, how many times each ran), with faults (unreachable
// servers, connections cut by a proxy, servers stopped mid-call, deadlines, cancellation,
// unknown methods, size limits, a closed ClientConn). Where grpc-go's behavior has a choice the
// model widens (the code of a transport failure, which the model may make any non-OK code), the
// test checks grpc-go's usual outcome, which the model's Go choices also take.
package grpcdifftest_test

import (
	"context"
	"fmt"
	"io"
	"net"
	"sort"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"

	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/health"
	healthpb "google.golang.org/grpc/health/grpc_health_v1"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/peer"
	"google.golang.org/grpc/resolver"
	"google.golang.org/grpc/resolver/manual"
	"google.golang.org/grpc/status"

	"models.lab/internal/grpcdifftest/svc"
)

var ids atomic.Uint64

// fresh is a fresh call id.
func fresh() string { return "c" + strconv.FormatUint(ids.Add(1), 10) }

// serveOpts starts a server for srv with opts on a fresh loopback address.
func serveOpts(t *testing.T, srv svc.EchoServer, opts ...grpc.ServerOption) (*grpc.Server, string) {
	t.Helper()
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	s := grpc.NewServer(opts...)
	svc.RegisterEchoServer(s, srv)
	go s.Serve(l)
	t.Cleanup(s.Stop)
	return s, l.Addr().String()
}

func serve(t *testing.T) (*svc.Server, string) {
	srv := svc.New()
	_, addr := serveOpts(t, srv)
	return srv, addr
}

func dialOpts(t *testing.T, addr string, opts ...grpc.DialOption) (*grpc.ClientConn, svc.EchoClient) {
	t.Helper()
	opts = append([]grpc.DialOption{grpc.WithTransportCredentials(insecure.NewCredentials())}, opts...)
	cc, err := grpc.NewClient(addr, opts...)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { cc.Close() })
	return cc, svc.NewEchoClient(cc)
}

func dial(t *testing.T, addr string) (*grpc.ClientConn, svc.EchoClient) {
	return dialOpts(t, addr)
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
		t.Fatalf("not a status error: %T %v", err, err)
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

// wantDeadline checks err is the end of a call whose deadline passed: DeadlineExceeded, with the
// client's message or the message of the server's RST_STREAM (whichever deadline fires first).
func wantDeadline(t *testing.T, err error) {
	t.Helper()
	wantStatus(t, err, codes.DeadlineExceeded, "")
	if m := status.Convert(err).Message(); m != "context deadline exceeded" && m != "stream terminated by RST_STREAM with error code: CANCEL" {
		t.Fatalf("message %q", m)
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

// mdString is md as a sorted, comparable string.
func mdString(md metadata.MD) string {
	var ks []string
	for k, vs := range md {
		ks = append(ks, fmt.Sprintf("%s=%q", k, vs))
	}
	sort.Strings(ks)
	return strings.Join(ks, " ")
}

func TestUnary(t *testing.T) {
	srv, addr := serve(t)
	_, c := dial(t, addr)
	id := fresh()
	r, err := c.Unary(ctx5(t), svc.M(id+" echo héllo"))
	if err != nil || r.GetValue() != "héllo" {
		t.Fatal(r, err)
	}
	if srv.Runs(id) != 1 {
		t.Fatalf("runs %d", srv.Runs(id))
	}
	s := srv.Seen(id)
	if !s.HasDeadline || !s.HasPeer || s.Method != svc.Echo_Unary_FullMethodName {
		t.Fatalf("seen %+v", s)
	}
	// the metadata a handler sees: grpc-go's reserved keys as its transport adds them
	want := fmt.Sprintf(`:authority=["%s"] content-type=["application/grpc"] user-agent=["grpc-go/1.84.0"]`, addr)
	if got := mdString(s.MD); got != want {
		t.Fatalf("incoming md %s, want %s", got, want)
	}
	if s.PeerLocal != addr {
		t.Fatalf("peer's local address %q", s.PeerLocal)
	}
}

func TestMetadata(t *testing.T) {
	srv, addr := serve(t)
	_, c := dialOpts(t, addr, grpc.WithUserAgent("ua/1"), grpc.WithAuthority("auth.example"))
	id := fresh()
	ctx := metadata.AppendToOutgoingContext(ctx5(t), "x", "1", "X", "2", "y-bin", "\x00\x01\xff")
	ctx = metadata.AppendToOutgoingContext(ctx, "x", "3")
	var hdr, trl metadata.MD
	var p peer.Peer
	r, err := c.Unary(ctx, svc.M(id+" md"), grpc.Header(&hdr), grpc.Trailer(&trl), grpc.Peer(&p))
	if err != nil || r.GetValue() != "md" {
		t.Fatal(r, err)
	}
	want := `:authority=["auth.example"] content-type=["application/grpc"] user-agent=["ua/1 grpc-go/1.84.0"] x=["1" "2" "3"] y-bin=["\x00\x01\xff"]`
	if got := mdString(srv.Seen(id).MD); got != want {
		t.Fatalf("incoming md %s, want %s", got, want)
	}
	if got := mdString(hdr); got != `content-type=["application/grpc"] k-bin=["\x00\xff"] k=["h"]` {
		t.Fatalf("header %s", got)
	}
	if got := mdString(trl); got != `k=["t"]` {
		t.Fatalf("trailer %s", got)
	}
	if p.Addr == nil || p.Addr.String() != addr || p.LocalAddr == nil || p.AuthInfo == nil ||
		p.AuthInfo.AuthType() != "insecure" {
		t.Fatalf("peer %+v", p)
	}
	// an invalid key fails before anything is sent
	_, err = c.Unary(metadata.AppendToOutgoingContext(ctx5(t), "bad key", "v"), svc.M(fresh()+" echo"))
	wantStatus(t, err, codes.Internal, "")
}

func TestSendHeaderTwice(t *testing.T) {
	_, addr := serve(t)
	_, c := dial(t, addr)
	var hdr metadata.MD
	r, err := c.Unary(ctx5(t), svc.M(fresh()+" sendheader"), grpc.Header(&hdr))
	if err != nil || r.GetValue() != "Internal|rpc error: code = Internal desc = transport: SendHeader called multiple times" {
		t.Fatal(r, err)
	}
	if got := mdString(hdr); got != `content-type=["application/grpc"] k=["1"]` {
		t.Fatalf("header %s", got)
	}
}

func TestConcurrent(t *testing.T) {
	srv, addr := serve(t)
	_, c := dial(t, addr)
	var wg sync.WaitGroup
	errs := make(chan error, 200)
	for i := 0; i < 200; i++ {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			id := fresh()
			r, err := c.Unary(context.Background(), svc.M(id+" echo "+strconv.Itoa(i)))
			if err != nil || r.GetValue() != strconv.Itoa(i) || srv.Runs(id) != 1 {
				errs <- fmt.Errorf("bad concurrent call: %v %v", r, err)
			}
		}(i)
	}
	wg.Wait()
	close(errs)
	for err := range errs {
		t.Fatal(err)
	}
}

func TestHandlerErrors(t *testing.T) {
	srv, addr := serve(t)
	_, c := dial(t, addr)
	var hdr, trl metadata.MD
	id := fresh()
	_, err := c.Unary(ctx5(t), svc.M(id+" err 3 bad arg: 100%\n¡ok!"), grpc.Header(&hdr), grpc.Trailer(&trl))
	wantStatus(t, err, codes.InvalidArgument, "bad arg: 100%\n¡ok!")
	// a trailers-only response: no header; the trailer holds the content type
	if hdr != nil {
		t.Fatalf("header %v", hdr)
	}
	if got := mdString(trl); got != `content-type=["application/grpc"]` {
		t.Fatalf("trailer %s", got)
	}
	_, err = c.Unary(ctx5(t), svc.M(fresh()+" plain plain failure"))
	wantStatus(t, err, codes.Unknown, "plain failure")
	ctx, cancel := context.WithTimeout(context.Background(), 100*time.Millisecond)
	defer cancel()
	id = fresh()
	_, err = c.Unary(ctx, svc.M(id+" ctxerr"))
	wantDeadline(t, err)
	eventually(t, "the handler's end", func() bool { s := srv.Seen(id); return s != nil && s.CtxErr != nil })
	// the server's own deadline, or the client's RST_STREAM when its deadline expires: either
	if e := srv.Seen(id).CtxErr; e != context.DeadlineExceeded && e != context.Canceled {
		t.Fatalf("handler's ctx err %v", e)
	}
	// a header, then a failure
	hdr, trl = nil, nil
	_, err = c.Unary(ctx5(t), svc.M(fresh()+" hdronly 9"), grpc.Header(&hdr), grpc.Trailer(&trl))
	wantStatus(t, err, codes.FailedPrecondition, "after header")
	if got := mdString(hdr); got != `content-type=["application/grpc"] k=["h"]` {
		t.Fatalf("header %s", got)
	}
	if len(trl) != 0 {
		t.Fatalf("trailer %v", trl)
	}
}

func TestUnknownMethod(t *testing.T) {
	_, addr := serve(t)
	cc, _ := dial(t, addr)
	err := cc.Invoke(ctx5(t), "/difftest.Echo/Mul", svc.M(""), new(svc.Msg))
	wantStatus(t, err, codes.Unimplemented, "unknown method Mul for service difftest.Echo")
	err = cc.Invoke(ctx5(t), "/nope.Nope/Add", svc.M(""), new(svc.Msg))
	wantStatus(t, err, codes.Unimplemented, "unknown service nope.Nope")
	err = cc.Invoke(ctx5(t), "/noslash", svc.M(""), new(svc.Msg))
	wantStatus(t, err, codes.Unimplemented, `malformed method name: "/noslash"`)
}

func TestUnknownServiceHandler(t *testing.T) {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	s := grpc.NewServer(grpc.UnknownServiceHandler(func(srv any, stream grpc.ServerStream) error {
		m, _ := grpc.MethodFromServerStream(stream)
		return status.Error(codes.NotFound, "no "+m)
	}))
	go s.Serve(l)
	defer s.Stop()
	cc, _ := dial(t, l.Addr().String())
	err = cc.Invoke(ctx5(t), "/a.B/C", svc.M(""), new(svc.Msg))
	wantStatus(t, err, codes.NotFound, "no /a.B/C")
}

func TestDeadline(t *testing.T) {
	srv, addr := serve(t)
	_, c := dial(t, addr)
	id := fresh()
	ctx, cancel := context.WithTimeout(context.Background(), 200*time.Millisecond)
	defer cancel()
	_, err := c.Unary(ctx, svc.M(id+" block"))
	// the client's deadline, or the server's (its RST_STREAM CANCEL): the message differs
	wantDeadline(t, err)
	eventually(t, "the handler's context to be done", func() bool { s := srv.Seen(id); return s != nil && s.CtxErr != nil })
	if e := srv.Seen(id).CtxErr; e != context.DeadlineExceeded && e != context.Canceled {
		t.Fatalf("handler's ctx err %v", e)
	}
	// the ClientConn is still usable
	if _, err := c.Unary(ctx5(t), svc.M(fresh()+" echo")); err != nil {
		t.Fatal(err)
	}
	// a deadline already past: nothing is sent
	ctx, cancel = context.WithDeadline(context.Background(), time.Now().Add(-time.Second))
	defer cancel()
	id = fresh()
	_, err = c.Unary(ctx, svc.M(id+" echo"))
	wantStatus(t, err, codes.DeadlineExceeded, "context deadline exceeded")
	time.Sleep(50 * time.Millisecond)
	if srv.Runs(id) != 0 {
		t.Fatalf("runs %d", srv.Runs(id))
	}
}

func TestCancel(t *testing.T) {
	srv, addr := serve(t)
	_, c := dial(t, addr)
	id := fresh()
	ctx, cancel := context.WithCancel(context.Background())
	go func() {
		eventually(t, "the handler to run", func() bool { return srv.Runs(id) == 1 })
		cancel()
	}()
	_, err := c.Unary(ctx, svc.M(id+" block"))
	wantStatus(t, err, codes.Canceled, "context canceled")
	eventually(t, "the handler's context to be done", func() bool { s := srv.Seen(id); return s != nil && s.CtxErr != nil })
	if e := srv.Seen(id).CtxErr; e != context.Canceled {
		t.Fatalf("handler's ctx err %v", e)
	}
	// canceled before the call: nothing is sent
	ctx, cancel = context.WithCancel(context.Background())
	cancel()
	id = fresh()
	_, err = c.Unary(ctx, svc.M(id+" echo"))
	wantStatus(t, err, codes.Canceled, "context canceled")
	time.Sleep(50 * time.Millisecond)
	if srv.Runs(id) != 0 {
		t.Fatalf("runs %d", srv.Runs(id))
	}
}

func TestSizeLimits(t *testing.T) {
	srv, addr := serve(t)
	_, c := dial(t, addr)
	// the server's default receive limit (4 MiB)
	id := fresh()
	big := strings.Repeat("y", 4*1024*1024)
	_, err := c.Unary(ctx5(t), svc.M(id+" echo "+big))
	wantStatus(t, err, codes.ResourceExhausted, fmt.Sprintf("grpc: received message larger than max (%d vs. 4194304)", len(id)+6+len(big)+5))
	if srv.Runs(id) != 0 {
		t.Fatalf("runs %d", srv.Runs(id))
	}
	// the client's default receive limit
	id = fresh()
	_, err = c.Unary(ctx5(t), svc.M(id+" big 4194305"))
	wantStatus(t, err, codes.ResourceExhausted, "grpc: received message larger than max (4194310 vs. 4194304)")
	if srv.Runs(id) != 1 {
		t.Fatalf("runs %d", srv.Runs(id))
	}
	// the call options' limits
	_, err = c.Unary(ctx5(t), svc.M(fresh()+" echo 0123456789"), grpc.MaxCallSendMsgSize(10))
	wantStatus(t, err, codes.ResourceExhausted, "")
	if !strings.HasPrefix(status.Convert(err).Message(), "trying to send message larger than max (") {
		t.Fatal(err)
	}
	_, err = c.Unary(ctx5(t), svc.M(fresh()+" big 100"), grpc.MaxCallRecvMsgSize(50))
	wantStatus(t, err, codes.ResourceExhausted, "grpc: received message larger than max (102 vs. 50)")
	// just under the limit
	if _, err := c.Unary(ctx5(t), svc.M(fresh()+" big 4194000")); err != nil {
		t.Fatal(err)
	}
	// the server's options
	srv2 := svc.New()
	_, addr2 := serveOpts(t, srv2, grpc.MaxRecvMsgSize(100), grpc.MaxSendMsgSize(100))
	_, c2 := dial(t, addr2)
	_, err = c2.Unary(ctx5(t), svc.M(fresh()+" big 200"))
	wantStatus(t, err, codes.ResourceExhausted, "trying to send message larger than max (203 vs. 100)")
	_, err = c2.Unary(ctx5(t), svc.M(fresh()+" echo "+strings.Repeat("z", 200)))
	wantStatus(t, err, codes.ResourceExhausted, "")
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
	_, c := dial(t, addr)
	_, err := c.Unary(ctx5(t), svc.M(fresh()+" echo"))
	wantStatus(t, err, codes.Unavailable, "")
	// waiting for ready: the call waits for the server
	ctx, cancel := context.WithTimeout(context.Background(), 300*time.Millisecond)
	defer cancel()
	_, err = c.Unary(ctx, svc.M(fresh()+" echo"), grpc.WaitForReady(true))
	wantStatus(t, err, codes.DeadlineExceeded, "")
}

func TestWaitForReady(t *testing.T) {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	addr := l.Addr().String()
	l.Close()
	_, c := dial(t, addr)
	srv := svc.New()
	go func() {
		time.Sleep(300 * time.Millisecond)
		l, err := net.Listen("tcp", addr)
		if err != nil {
			return
		}
		s := grpc.NewServer()
		svc.RegisterEchoServer(s, srv)
		t.Cleanup(s.Stop)
		s.Serve(l)
	}()
	id := fresh()
	ctx, cancel := context.WithTimeout(context.Background(), 20*time.Second)
	defer cancel()
	r, err := c.Unary(ctx, svc.M(id+" echo up"), grpc.WaitForReady(true))
	if err != nil || r.GetValue() != "up" || srv.Runs(id) != 1 {
		t.Fatal(r, err)
	}
}

func TestNoCredentials(t *testing.T) {
	cc, err := grpc.NewClient("127.0.0.1:1")
	if err == nil || cc != nil || err.Error() != "grpc: no transport security set (use grpc.WithTransportCredentials(insecure.NewCredentials()) explicitly or set credentials)" {
		t.Fatalf("NewClient without credentials: %v %v", cc, err)
	}
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
	srv, addr := serve(t)
	p := newProxy(t, addr)
	_, c := dial(t, p.l.Addr().String())
	if _, err := c.Unary(ctx5(t), svc.M(fresh()+" echo")); err != nil {
		t.Fatal(err)
	}
	p.cut()
	ok := false
	for i := 0; i < 300 && !ok; i++ {
		id := fresh()
		_, err := c.Unary(ctx5(t), svc.M(id+" echo"))
		if srv.Runs(id) > 1 {
			t.Fatalf("runs %d", srv.Runs(id))
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
// its handler ran once, whose context is then canceled.
func TestCutWhileWaiting(t *testing.T) {
	srv, addr := serve(t)
	p := newProxy(t, addr)
	_, c := dial(t, p.l.Addr().String())
	id := fresh()
	go func() {
		eventually(t, "the handler to run", func() bool { return srv.Runs(id) == 1 })
		p.cut()
	}()
	_, err := c.Unary(ctx5(t), svc.M(id+" block"))
	wantStatus(t, err, codes.Unavailable, "")
	eventually(t, "the handler's context to be done", func() bool { s := srv.Seen(id); return s != nil && s.CtxErr != nil })
	if e := srv.Seen(id).CtxErr; e != context.Canceled {
		t.Fatalf("handler's ctx err %v", e)
	}
}

// TestStopMidCall: Stop while a handler runs: the call fails with Unavailable, the handler's
// context is canceled; Serve returns nil; a later call fails.
func TestStopMidCall(t *testing.T) {
	srv := svc.New()
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	s := grpc.NewServer()
	svc.RegisterEchoServer(s, srv)
	served := make(chan error, 1)
	go func() { served <- s.Serve(l) }()
	_, c := dial(t, l.Addr().String())
	id := fresh()
	go func() {
		eventually(t, "the handler to run", func() bool { return srv.Runs(id) == 1 })
		s.Stop()
	}()
	_, err = c.Unary(ctx5(t), svc.M(id+" block"))
	wantStatus(t, err, codes.Unavailable, "")
	if err := <-served; err != nil {
		t.Fatalf("Serve: %v", err)
	}
	eventually(t, "the handler's context to be done", func() bool { s := srv.Seen(id); return s != nil && s.CtxErr != nil })
	_, err = c.Unary(ctx5(t), svc.M(fresh()+" echo"))
	wantStatus(t, err, codes.Unavailable, "")
}

// TestGracefulStop: GracefulStop waits for the running handler, whose call succeeds; Serve
// returns nil; later calls fail.
func TestGracefulStop(t *testing.T) {
	srv := svc.New()
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	s := grpc.NewServer()
	svc.RegisterEchoServer(s, srv)
	served := make(chan error, 1)
	go func() { served <- s.Serve(l) }()
	_, c := dial(t, l.Addr().String())
	id := fresh()
	stopped := make(chan struct{})
	go func() {
		eventually(t, "the handler to run", func() bool { return srv.Runs(id) == 1 })
		s.GracefulStop()
		close(stopped)
	}()
	r, err := c.Unary(ctx5(t), svc.M(id+" slow 300ms done"))
	if err != nil || r.GetValue() != "done" {
		t.Fatal(r, err)
	}
	<-stopped
	if err := <-served; err != nil {
		t.Fatalf("Serve: %v", err)
	}
	_, err = c.Unary(ctx5(t), svc.M(fresh()+" echo"))
	wantStatus(t, err, codes.Unavailable, "")
	// Serve after Stop
	l2, _ := net.Listen("tcp", "127.0.0.1:0")
	if err := s.Serve(l2); err != grpc.ErrServerStopped {
		t.Fatalf("Serve after stop: %v", err)
	}
}

func TestClose(t *testing.T) {
	_, addr := serve(t)
	cc, err := grpc.NewClient(addr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	c := svc.NewEchoClient(cc)
	if _, err := c.Unary(ctx5(t), svc.M(fresh()+" echo")); err != nil {
		t.Fatal(err)
	}
	if err := cc.Close(); err != nil {
		t.Fatal(err)
	}
	_, err = c.Unary(ctx5(t), svc.M(fresh()+" echo"))
	wantStatus(t, err, codes.Canceled, "grpc: the client connection is closing")
	if err := cc.Close(); err != grpc.ErrClientConnClosing {
		t.Fatalf("second Close: %v", err)
	}
	if cc.GetState().String() != "SHUTDOWN" {
		t.Fatalf("state %v", cc.GetState())
	}
}

// TestCloseMidCall: Close while a call waits: the call fails.
func TestCloseMidCall(t *testing.T) {
	srv, addr := serve(t)
	cc, err := grpc.NewClient(addr, grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	c := svc.NewEchoClient(cc)
	id := fresh()
	go func() {
		eventually(t, "the handler to run", func() bool { return srv.Runs(id) == 1 })
		cc.Close()
	}()
	_, err = c.Unary(ctx5(t), svc.M(id+" block"))
	if c := status.Code(err); c != codes.Unavailable && c != codes.Canceled {
		t.Fatalf("call at Close: %v", err)
	}
	eventually(t, "the handler's context to be done", func() bool { s := srv.Seen(id); return s != nil && s.CtxErr != nil })
}

func TestInterceptors(t *testing.T) {
	var order []string
	var mu sync.Mutex
	log := func(s string) { mu.Lock(); order = append(order, s); mu.Unlock() }
	ui := func(name string) grpc.UnaryServerInterceptor {
		return func(ctx context.Context, req any, info *grpc.UnaryServerInfo, h grpc.UnaryHandler) (any, error) {
			log("s" + name + ":" + info.FullMethod)
			return h(ctx, req)
		}
	}
	si := func(name string) grpc.StreamServerInterceptor {
		return func(srv any, ss grpc.ServerStream, info *grpc.StreamServerInfo, h grpc.StreamHandler) error {
			log(fmt.Sprintf("ss%s:%s:%v:%v", name, info.FullMethod, info.IsClientStream, info.IsServerStream))
			return h(srv, ss)
		}
	}
	srv := svc.New()
	_, addr := serveOpts(t, srv, grpc.UnaryInterceptor(ui("0")), grpc.ChainUnaryInterceptor(ui("1"), ui("2")),
		grpc.ChainStreamInterceptor(si("1"), si("2")))
	cu := func(name string) grpc.UnaryClientInterceptor {
		return func(ctx context.Context, method string, req, reply any, cc *grpc.ClientConn, inv grpc.UnaryInvoker, opts ...grpc.CallOption) error {
			log("c" + name + ":" + method)
			return inv(ctx, method, req, reply, cc, opts...)
		}
	}
	cs := func(name string) grpc.StreamClientInterceptor {
		return func(ctx context.Context, desc *grpc.StreamDesc, cc *grpc.ClientConn, method string, st grpc.Streamer, opts ...grpc.CallOption) (grpc.ClientStream, error) {
			log("cs" + name + ":" + method)
			return st(ctx, desc, cc, method, opts...)
		}
	}
	_, c := dialOpts(t, addr, grpc.WithChainUnaryInterceptor(cu("1"), cu("2")), grpc.WithStreamInterceptor(cs("0")),
		grpc.WithChainStreamInterceptor(cs("1")))
	if _, err := c.Unary(ctx5(t), svc.M(fresh()+" echo")); err != nil {
		t.Fatal(err)
	}
	st, err := c.ServerStream(ctx5(t), svc.M(fresh()+" stream 1"))
	if err != nil {
		t.Fatal(err)
	}
	for {
		if _, err := st.Recv(); err != nil {
			break
		}
	}
	mu.Lock()
	got := strings.Join(order, " ")
	mu.Unlock()
	want := "c1:/difftest.Echo/Unary c2:/difftest.Echo/Unary s0:/difftest.Echo/Unary s1:/difftest.Echo/Unary s2:/difftest.Echo/Unary " +
		"cs0:/difftest.Echo/ServerStream cs1:/difftest.Echo/ServerStream ss1:/difftest.Echo/ServerStream:false:true ss2:/difftest.Echo/ServerStream:false:true"
	if got != want {
		t.Fatalf("order %s\nwant  %s", got, want)
	}
}

func TestServerStream(t *testing.T) {
	srv, addr := serve(t)
	_, c := dial(t, addr)
	id := fresh()
	st, err := c.ServerStream(ctx5(t), svc.M(id+" stream 5"))
	if err != nil {
		t.Fatal(err)
	}
	hdr, err := st.Header()
	if err != nil || mdString(hdr) != `content-type=["application/grpc"] sh=["1"]` {
		t.Fatal(hdr, err)
	}
	var got []string
	for {
		m, err := st.Recv()
		if err == io.EOF {
			break
		}
		if err != nil {
			t.Fatal(err)
		}
		got = append(got, m.GetValue())
	}
	if strings.Join(got, ",") != "1,2,3,4,5" {
		t.Fatal(got)
	}
	if mdString(st.Trailer()) != `st=["1"]` {
		t.Fatal(st.Trailer())
	}
	if srv.Runs(id) != 1 {
		t.Fatal(srv.Runs(id))
	}
	// a stream that fails
	st, err = c.ServerStream(ctx5(t), svc.M(fresh()+" err 5 gone"))
	if err != nil {
		t.Fatal(err)
	}
	hdr, err = st.Header()
	if hdr != nil || err != nil {
		t.Fatal(hdr, err)
	}
	_, err = st.Recv()
	wantStatus(t, err, codes.NotFound, "gone")
	_, err = st.Recv()
	wantStatus(t, err, codes.NotFound, "gone")
	if mdString(st.Trailer()) != `content-type=["application/grpc"]` {
		t.Fatal(st.Trailer())
	}
}

func TestServerStreamCancel(t *testing.T) {
	srv, addr := serve(t)
	_, c := dial(t, addr)
	id := fresh()
	ctx, cancel := context.WithCancel(context.Background())
	st, err := c.ServerStream(ctx, svc.M(id+" forever"))
	if err != nil {
		t.Fatal(err)
	}
	for i := 1; i <= 10; i++ {
		m, err := st.Recv()
		if err != nil || m.GetValue() != strconv.Itoa(i) {
			t.Fatal(m, err)
		}
	}
	cancel()
	for {
		_, err := st.Recv()
		if err != nil {
			wantStatus(t, err, codes.Canceled, "context canceled")
			break
		}
	}
	eventually(t, "the handler's end", func() bool { s := srv.Seen(id); return s != nil && s.CtxErr != nil })
	if e := srv.Seen(id).CtxErr; e != context.Canceled {
		t.Fatalf("handler's ctx err %v", e)
	}
}

func TestClientStream(t *testing.T) {
	srv, addr := serve(t)
	_, c := dial(t, addr)
	id := fresh()
	st, err := c.ClientStream(ctx5(t))
	if err != nil {
		t.Fatal(err)
	}
	for _, v := range []string{" a", " b", " c"} {
		if err := st.Send(svc.M(id + v)); err != nil {
			t.Fatal(err)
		}
	}
	r, err := st.CloseAndRecv()
	if err != nil || r.GetValue() != id+" a,"+id+" b,"+id+" c" {
		t.Fatal(r, err)
	}
	if srv.Runs(id) != 1 {
		t.Fatal(srv.Runs(id))
	}
	// the server fails early: sends after its status fail with io.EOF, the status is Recv's
	st, err = c.ClientStream(ctx5(t))
	if err != nil {
		t.Fatal(err)
	}
	if err := st.Send(svc.M(fresh() + " err 10 aborted")); err != nil {
		t.Fatal(err)
	}
	var serr error
	for i := 0; i < 1000; i++ {
		if serr = st.Send(svc.M("more")); serr != nil {
			break
		}
		time.Sleep(time.Millisecond)
	}
	if serr != io.EOF {
		t.Fatalf("send after the server's end: %v", serr)
	}
	_, err = st.CloseAndRecv()
	wantStatus(t, err, codes.Aborted, "aborted")
	// no message, then close: the server replies with the empty join
	st, err = c.ClientStream(ctx5(t))
	if err != nil {
		t.Fatal(err)
	}
	r, err = st.CloseAndRecv()
	if err != nil || r.GetValue() != "" {
		t.Fatal(r, err)
	}
}

func TestBidi(t *testing.T) {
	_, addr := serve(t)
	_, c := dial(t, addr)
	st, err := c.Bidi(ctx5(t))
	if err != nil {
		t.Fatal(err)
	}
	id := fresh()
	// one sender and one receiver at the same time
	done := make(chan error, 1)
	go func() {
		for i := 0; i < 100; i++ {
			if err := st.Send(svc.M(id + " echo " + strconv.Itoa(i))); err != nil {
				done <- err
				return
			}
		}
		done <- st.CloseSend()
	}()
	for i := 0; i < 100; i++ {
		m, err := st.Recv()
		if err != nil || m.GetValue() != strconv.Itoa(i) {
			t.Fatal(m, err)
		}
	}
	if _, err := st.Recv(); err != io.EOF {
		t.Fatal(err)
	}
	if err := <-done; err != nil {
		t.Fatal(err)
	}
	// SendMsg after CloseSend
	if err := st.SendMsg(svc.M("x")); err == nil {
		t.Fatal("send after CloseSend")
	}
	// the server fails mid-stream
	st, err = c.Bidi(ctx5(t))
	if err != nil {
		t.Fatal(err)
	}
	id = fresh()
	st.Send(svc.M(id + " echo 1"))
	if m, err := st.Recv(); err != nil || m.GetValue() != "1" {
		t.Fatal(m, err)
	}
	st.Send(svc.M(id + " err 7 denied"))
	_, err = st.Recv()
	wantStatus(t, err, codes.PermissionDenied, "denied")
}

func TestStreamDeadline(t *testing.T) {
	_, addr := serve(t)
	_, c := dial(t, addr)
	ctx, cancel := context.WithTimeout(context.Background(), 200*time.Millisecond)
	defer cancel()
	st, err := c.Bidi(ctx)
	if err != nil {
		t.Fatal(err)
	}
	_, err = st.Recv()
	wantDeadline(t, err)
}

func TestHealth(t *testing.T) {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	s := grpc.NewServer()
	hs := health.NewServer()
	healthpb.RegisterHealthServer(s, hs)
	go s.Serve(l)
	defer s.Stop()
	cc, _ := dial(t, l.Addr().String())
	hc := healthpb.NewHealthClient(cc)
	r, err := hc.Check(ctx5(t), &healthpb.HealthCheckRequest{})
	if err != nil || r.Status != healthpb.HealthCheckResponse_SERVING {
		t.Fatal(r, err)
	}
	_, err = hc.Check(ctx5(t), &healthpb.HealthCheckRequest{Service: "nope"})
	wantStatus(t, err, codes.NotFound, "unknown service")
	w, err := hc.Watch(ctx5(t), &healthpb.HealthCheckRequest{Service: "svc"})
	if err != nil {
		t.Fatal(err)
	}
	m, err := w.Recv()
	if err != nil || m.Status != healthpb.HealthCheckResponse_SERVICE_UNKNOWN {
		t.Fatal(m, err)
	}
	hs.SetServingStatus("svc", healthpb.HealthCheckResponse_NOT_SERVING)
	m, err = w.Recv()
	if err != nil || m.Status != healthpb.HealthCheckResponse_NOT_SERVING {
		t.Fatal(m, err)
	}
}

// TestManualResolver: clientv3's way, a manual resolver with the round-robin service config and
// endpoints; a call waits for the resolver's first update.
func TestManualResolver(t *testing.T) {
	srv, addr := serve(t)
	_, addr2 := serve(t)
	r := manual.NewBuilderWithScheme("difftest")
	cc, c := dialOpts(t, "difftest:///x", grpc.WithResolvers(r))
	id := fresh()
	done := make(chan error, 1)
	go func() {
		_, err := c.Unary(ctx5(t), svc.M(id+" echo"), grpc.WaitForReady(true))
		done <- err
	}()
	time.Sleep(100 * time.Millisecond)
	select {
	case err := <-done:
		t.Fatalf("returned before the resolver's update: %v", err)
	default:
	}
	eventually(t, "the resolver's build", func() bool { return r.CC() != nil })
	sc := r.CC().ParseServiceConfig(`{"loadBalancingPolicy": "round_robin"}`)
	r.UpdateState(resolver.State{
		Endpoints:     []resolver.Endpoint{{Addresses: []resolver.Address{{Addr: addr}}}},
		ServiceConfig: sc,
	})
	if err := <-done; err != nil {
		t.Fatal(err)
	}
	if srv.Runs(id) != 1 {
		t.Fatal(srv.Runs(id))
	}
	_ = addr2
	if cc.Target() != "difftest:///x" || cc.CanonicalTarget() != "difftest:///x" {
		t.Fatal(cc.Target(), cc.CanonicalTarget())
	}
}

// audCreds is per-RPC credentials that record the audience (uri) grpc passes and add one key.
type audCreds struct {
	mu   sync.Mutex
	auds []string
}

func (a *audCreds) GetRequestMetadata(_ context.Context, uri ...string) (map[string]string, error) {
	a.mu.Lock()
	defer a.mu.Unlock()
	a.auds = append(a.auds, strings.Join(uri, ","))
	return map[string]string{"Tok": "t1"}, nil
}

func (a *audCreds) RequireTransportSecurity() bool { return false }

// TestPerRPCCredsAudience: per-RPC credentials get the audience grpc-go's createHeaderFields makes
// (the service's URL: the method up to its last '/', the authority without a ":443" suffix; the
// model's backwards byte loop in place of strings.LastIndex), and their keys reach the handler
// lower-cased.
func TestPerRPCCredsAudience(t *testing.T) {
	srv, addr := serve(t)
	for _, tc := range []struct{ authority, want string }{
		{"auth.example:443", "https://auth.example/difftest.Echo"},
		{"auth.example:8443", "https://auth.example:8443/difftest.Echo"},
	} {
		creds := &audCreds{}
		_, c := dialOpts(t, addr, grpc.WithPerRPCCredentials(creds), grpc.WithAuthority(tc.authority))
		id := fresh()
		r, err := c.Unary(ctx5(t), svc.M(id+" echo a"))
		if err != nil || r.GetValue() != "a" {
			t.Fatal(r, err)
		}
		creds.mu.Lock()
		auds := append([]string(nil), creds.auds...)
		creds.mu.Unlock()
		if len(auds) != 1 || auds[0] != tc.want {
			t.Fatalf("audiences %q, want [%q]", auds, tc.want)
		}
		if vs := srv.Seen(id).MD["tok"]; len(vs) != 1 || vs[0] != "t1" {
			t.Fatalf("incoming md %s", mdString(srv.Seen(id).MD))
		}
	}
}

// TestServingStatusString: the health status's String (the model's switch in place of protoimpl's
// EnumStringOf, models/grpc/health/grpc_health_v1/health.pb.go): the four names, else the number in
// decimal, by value and through a pointer.
func TestServingStatusString(t *testing.T) {
	for _, tc := range []struct {
		v    int32
		want string
	}{
		{0, "UNKNOWN"}, {1, "SERVING"}, {2, "NOT_SERVING"}, {3, "SERVICE_UNKNOWN"}, {4, "4"},
		{-1, "-1"}, {1 << 30, "1073741824"}, {2147483647, "2147483647"}, {-2147483648, "-2147483648"},
	} {
		x := healthpb.HealthCheckResponse_ServingStatus(tc.v)
		r := &healthpb.HealthCheckResponse{Status: x}
		if got := x.String(); got != tc.want {
			t.Errorf("ServingStatus(%d).String() = %q, want %q", tc.v, got, tc.want)
		}
		if got := (&r.Status).String(); got != tc.want {
			t.Errorf("(&ServingStatus(%d)).String() = %q, want %q", tc.v, got, tc.want)
		}
	}
}
