// Package streamctx checks the claims of the trusted texts of k8s 7f-4 (notes/k8s-7f4-freeze.md §2)
// about grpc's stream handler contexts and the specs a require-leader stream handler's context
// reaches, at the pins (grpc v1.84.0, go-grpc-middleware v2.3.4 / providers/prometheus v1.1.0,
// otelgrpc v0.71.0, etcd's fork):
//
//   - T-a (TestRunCtxChain): the context a stream handler's ServerStream returns is a chain of
//     *context.valueCtx, *context.cancelCtx and *context.timerCtx links over Background(), which
//     context.value() walks, so the chain form of its library values (ctxValue) holds; with and
//     without TLS, otelgrpc's stats handler, a client deadline and grpc-prometheus's interceptor;
//     no link is at one of the keys net/http's client reads (T-h0, http.netCtxOkC), through Serve
//     and through ServeHTTP; nor in a unary handler's context (TestRunCtxChainUnary, T-h6's
//     grpcRunCtx clause).
//   - T-b, as revised (TestIncomingOfValue; Revision 1 of the freeze note, B1): a *cancelCtx has
//     its parent's incoming metadata (metadata.incomingOf_cancelCtx), and etcd's require-leader
//     wrapper (*cancellableContext) its embedded context's (v3rpc.incomingOf_cancellableContext),
//     after its Cancel(ErrGRPCNoLeader) too; also a context whose Done, Err and Deadline panic and a
//     WithValue child. metadata.FromIncomingContext reads only Value(mdIncomingKey{}).
//   - T-c (TestRawStreamKey): the ServerStream an interceptor or handler receives is a pointer (grpc's
//     *serverStream, prometheus's *monitoredServerStream), a comparable map key, alone or in a
//     struct beside a pointer (etcd's serverStreamWithCtx); with and without otelgrpc's stats
//     handler, through Serve and ServeHTTP.
//   - T-f (TestRenewHTTPErrTiming): leasehttp.RenewHTTP over a *http.Transport calls the context's
//     Err() only once Done is closed (a context whose Err panics before Done is fine), and returns
//     an error when it is cancelled with an Err() of ErrGRPCNoLeader; on a context already
//     cancelled when it is called, Err() is called (on the caller's goroutine) and a *url.Error is
//     returned.
package streamctx

import (
	"context"
	"crypto/tls"
	"errors"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/http/httptest"
	"net/url"
	"reflect"
	"strings"
	"sync"
	"sync/atomic"
	"testing"
	"time"
	"unsafe"

	grpcprom "github.com/grpc-ecosystem/go-grpc-middleware/providers/prometheus"
	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/lease/leasehttp"
	"go.opentelemetry.io/contrib/instrumentation/google.golang.org/grpc/otelgrpc"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	oteltrace "go.opentelemetry.io/otel/trace"
	"google.golang.org/grpc"
	"google.golang.org/grpc/credentials"
	"google.golang.org/grpc/credentials/insecure"
	"google.golang.org/grpc/metadata"
	"google.golang.org/protobuf/proto"
	"google.golang.org/protobuf/types/known/emptypb"
)

var streamDesc = grpc.StreamDesc{StreamName: "S", ServerStreams: true, ClientStreams: true}

// startServer serves the bidirectional stream t.S/S with the handler h on localhost.
func startServer(t *testing.T, opts []grpc.ServerOption, h grpc.StreamHandler) *grpc.ClientConn {
	t.Helper()
	s := grpc.NewServer(opts...)
	s.RegisterService(&grpc.ServiceDesc{
		ServiceName: "t.S",
		HandlerType: (*any)(nil),
		Streams:     []grpc.StreamDesc{{StreamName: "S", Handler: h, ServerStreams: true, ClientStreams: true}},
	}, struct{}{})
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	go s.Serve(l)
	t.Cleanup(s.Stop)
	cc, err := grpc.NewClient(l.Addr().String(), grpc.WithTransportCredentials(insecure.NewCredentials()))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { cc.Close() })
	return cc
}

// startServerHTTP is startServer through grpc's ServeHTTP (an HTTP/2 TLS httptest server), the
// path etcd takes when it serves gRPC and HTTP on one port (cmux with TLS).
func startServerHTTP(t *testing.T, opts []grpc.ServerOption, h grpc.StreamHandler) *grpc.ClientConn {
	t.Helper()
	s := grpc.NewServer(opts...)
	s.RegisterService(&grpc.ServiceDesc{
		ServiceName: "t.S",
		HandlerType: (*any)(nil),
		Streams:     []grpc.StreamDesc{{StreamName: "S", Handler: h, ServerStreams: true, ClientStreams: true}},
	}, struct{}{})
	hs := httptest.NewUnstartedServer(s)
	hs.EnableHTTP2 = true
	hs.StartTLS()
	t.Cleanup(hs.Close)
	cc, err := grpc.NewClient(hs.Listener.Addr().String(),
		grpc.WithTransportCredentials(credentials.NewTLS(&tls.Config{InsecureSkipVerify: true})))
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { cc.Close() })
	return cc
}

// runStream opens t.S/S with outgoing metadata (and a deadline if dl) and waits for the handler.
func runStream(t *testing.T, cc *grpc.ClientConn, dl bool) {
	t.Helper()
	ctx := metadata.AppendToOutgoingContext(context.Background(), "token", "x", "hasleader", "true")
	if dl {
		var cancel context.CancelFunc
		ctx, cancel = context.WithTimeout(ctx, time.Minute)
		defer cancel()
	}
	cs, err := cc.NewStream(ctx, &streamDesc, "/t.S/S")
	if err != nil {
		t.Fatal(err)
	}
	if err := cs.RecvMsg(new(emptypb.Empty)); err != io.EOF {
		t.Fatalf("stream: %v", err)
	}
}

// field reads the (possibly unexported) field name of the struct v.
func field(v reflect.Value, name string) (reflect.Value, bool) {
	f := v.FieldByName(name)
	if !f.IsValid() {
		return f, false
	}
	return reflect.NewAt(f.Type(), unsafe.Pointer(f.UnsafeAddr())).Elem(), true
}

// chain lists the dynamic types of ctx's links, following the parent of each link of a type
// context.value() special-cases; it stops at the first link of another type.
func chain(ctx context.Context) []string {
	var tys []string
	for ctx != nil {
		ty := fmt.Sprintf("%T", ctx)
		tys = append(tys, ty)
		v := reflect.ValueOf(ctx)
		switch ty {
		case "*context.valueCtx", "*context.cancelCtx":
			p, _ := field(v.Elem(), "Context")
			ctx, _ = p.Interface().(context.Context)
		case "*context.timerCtx":
			cc, _ := field(v.Elem(), "cancelCtx")
			p, _ := field(cc, "Context")
			ctx, _ = p.Interface().(context.Context)
		default:
			return tys
		}
	}
	return tys
}

// chainKeys lists the dynamic types of the keys of ctx's *context.valueCtx links (as chain walks).
func chainKeys(ctx context.Context) []string {
	var tys []string
	for ctx != nil {
		v := reflect.ValueOf(ctx)
		switch fmt.Sprintf("%T", ctx) {
		case "*context.valueCtx":
			k, _ := field(v.Elem(), "key")
			tys = append(tys, fmt.Sprintf("%T", k.Interface()))
			p, _ := field(v.Elem(), "Context")
			ctx, _ = p.Interface().(context.Context)
		case "*context.cancelCtx":
			p, _ := field(v.Elem(), "Context")
			ctx, _ = p.Interface().(context.Context)
		case "*context.timerCtx":
			cc, _ := field(v.Elem(), "cancelCtx")
			p, _ := field(cc, "Context")
			ctx, _ = p.Interface().(context.Context)
		default:
			return tys
		}
	}
	return tys
}

// netKeyTys are the key types net/http's client reads (Addendum T-h0, http.netCtxOkC).
var netKeyTys = map[string]bool{"httptrace.clientEventContextKey": true, "nettrace.TraceKey": true,
	"nettrace.LookupIPAltResolverKey": true}

var chainTys = map[string]bool{"*context.valueCtx": true, "*context.cancelCtx": true,
	"*context.timerCtx": true, "context.backgroundCtx": true}

func TestRunCtxChain(t *testing.T) {
	for _, viaHTTP := range []bool{false, true} {
		for _, prom := range []bool{false, true} {
			for _, otel := range []bool{false, true} {
				for _, dl := range []bool{false, true} {
					name := fmt.Sprintf("http=%v prom=%v otel=%v deadline=%v", viaHTTP, prom, otel, dl)
					start := startServer
					if viaHTTP {
						start = startServerHTTP
					}
					var opts []grpc.ServerOption
					if prom {
						opts = append(opts, grpc.ChainStreamInterceptor(grpcprom.NewServerMetrics().StreamServerInterceptor()))
					}
					if otel {
						opts = append(opts, grpc.StatsHandler(otelgrpc.NewServerHandler(
							otelgrpc.WithTracerProvider(sdktrace.NewTracerProvider()))))
					}
					got := make(chan []string, 1)
					keys := make(chan []string, 1)
					cc := start(t, opts, func(_ any, ss grpc.ServerStream) error {
						got <- chain(ss.Context())
						keys <- chainKeys(ss.Context())
						return nil
					})
					runStream(t, cc, dl)
					tys := <-got
					for _, k := range <-keys {
						if netKeyTys[k] {
							t.Errorf("%s: a link at net/http's key %s", name, k)
						}
					}
					if tys[len(tys)-1] != "context.backgroundCtx" {
						t.Errorf("%s: chain does not end at Background(): %v", name, tys)
					}
					for _, ty := range tys {
						if !chainTys[ty] {
							t.Errorf("%s: link of type %s: %v", name, ty, tys)
						}
					}
					t.Logf("%s: %v", name, tys)
				}
			}
		}
	}
}

// TestRunCtxChainUnary: a unary handler's context (grpcRunCtx's unary claim, T-h6) has no link at
// one of net/http's client keys either, with and without otelgrpc's stats handler.
func TestRunCtxChainUnary(t *testing.T) {
	for _, otel := range []bool{false, true} {
		var opts []grpc.ServerOption
		if otel {
			opts = append(opts, grpc.StatsHandler(otelgrpc.NewServerHandler(
				otelgrpc.WithTracerProvider(sdktrace.NewTracerProvider()))))
		}
		got := make(chan []string, 1)
		keys := make(chan []string, 1)
		s := grpc.NewServer(opts...)
		s.RegisterService(&grpc.ServiceDesc{ServiceName: "t.U", HandlerType: (*any)(nil),
			Methods: []grpc.MethodDesc{{MethodName: "M", Handler: func(_ any, ctx context.Context,
				dec func(any) error, _ grpc.UnaryServerInterceptor) (any, error) {
				in := new(emptypb.Empty)
				if err := dec(in); err != nil {
					return nil, err
				}
				got <- chain(ctx)
				keys <- chainKeys(ctx)
				return new(emptypb.Empty), nil
			}}}}, struct{}{})
		l, err := net.Listen("tcp", "127.0.0.1:0")
		if err != nil {
			t.Fatal(err)
		}
		go s.Serve(l)
		cc, err := grpc.NewClient(l.Addr().String(), grpc.WithTransportCredentials(insecure.NewCredentials()))
		if err != nil {
			t.Fatal(err)
		}
		if err := cc.Invoke(context.Background(), "/t.U/M", new(emptypb.Empty), new(emptypb.Empty)); err != nil {
			t.Fatal(err)
		}
		tys, ks := <-got, <-keys
		for _, k := range ks {
			if netKeyTys[k] {
				t.Errorf("otel=%v: a link at net/http's key %s", otel, k)
			}
		}
		t.Logf("otel=%v: chain %v keys %v", otel, tys, ks)
		cc.Close()
		s.Stop()
	}
}

// cancellableContext is etcd's require-leader wrapper (v3rpc/interceptor.go), its methods but Err
// promoted from the embedded WithCancel child.
type cancellableContext struct {
	context.Context
	mu           sync.RWMutex
	cancel       context.CancelFunc
	cancelReason error
}

func (c *cancellableContext) Cancel(reason error) {
	c.mu.Lock()
	c.cancelReason = reason
	c.mu.Unlock()
	c.cancel()
}

func (c *cancellableContext) Err() error {
	c.mu.RLock()
	defer c.mu.RUnlock()
	if c.cancelReason != nil {
		return c.cancelReason
	}
	return c.Context.Err()
}

// valueOnly answers Value as its parent; its Done, Err and Deadline panic.
type valueOnly struct{ p context.Context }

func (c valueOnly) Deadline() (time.Time, bool) { panic("Deadline") }
func (c valueOnly) Done() <-chan struct{}       { panic("Done") }
func (c valueOnly) Err() error                  { panic("Err") }
func (c valueOnly) Value(k any) any             { return c.p.Value(k) }

type otherKey struct{}

func TestIncomingOfValue(t *testing.T) {
	type res struct {
		md metadata.MD
		ok bool
	}
	from := func(ctx context.Context) res { md, ok := metadata.FromIncomingContext(ctx); return res{md, ok} }
	got := make(chan []res, 1)
	cc := startServer(t, []grpc.ServerOption{
		grpc.ChainStreamInterceptor(grpcprom.NewServerMetrics().StreamServerInterceptor()),
		grpc.StatsHandler(otelgrpc.NewServerHandler(otelgrpc.WithTracerProvider(sdktrace.NewTracerProvider()))),
	}, func(_ any, ss grpc.ServerStream) error {
		ci := ss.Context()
		inner, cancel := context.WithCancel(ci)
		w := &cancellableContext{Context: inner, cancel: cancel}
		w.Cancel(rpctypes.ErrGRPCNoLeader) // done, Err() is ErrGRPCNoLeader: FromIncomingContext does not care
		got <- []res{from(ci), from(inner), from(w), from(valueOnly{w}), from(context.WithValue(w, otherKey{}, 1))}
		return nil
	})
	runStream(t, cc, false)
	rs := <-got
	if !rs[0].ok || len(rs[0].md["token"]) == 0 {
		t.Fatalf("handler's metadata: %v", rs[0])
	}
	for i, r := range rs[1:] {
		if !reflect.DeepEqual(r, rs[0]) {
			t.Errorf("derived context %d: %v, handler's %v", i+1, r, rs[0])
		}
	}
	// Two unrelated contexts holding the same MD value at the key.
	md := metadata.MD{"token": {"y"}, "Mixed": {"a", "b"}}
	c1 := metadata.NewIncomingContext(context.Background(), md)
	c2 := metadata.NewIncomingContext(context.WithValue(context.TODO(), otherKey{}, 2), md)
	if r1, r2 := from(c1), from(c2); !reflect.DeepEqual(r1, r2) || !r1.ok {
		t.Errorf("same MD value: %v vs %v", r1, r2)
	}
	// Nothing at the key: (nil, false) for both.
	if r1, r2 := from(context.Background()), from(valueOnly{context.TODO()}); r1.ok || r2.ok || r1.md != nil || r2.md != nil {
		t.Errorf("no metadata: %v vs %v", r1, r2)
	}
}

type serverStreamWithCtx struct {
	grpc.ServerStream
	ctx *cancellableContext
}

// TestRawStreamKey: with and without grpc-prometheus's interceptor and otelgrpc's stats handler,
// through Serve and through ServeHTTP (the review's m1).
func TestRawStreamKey(t *testing.T) {
	type variant struct{ prom, otel, http bool }
	var vs []variant
	for _, prom := range []bool{false, true} {
		for _, otel := range []bool{false, true} {
			for _, h := range []bool{false, true} {
				vs = append(vs, variant{prom, otel, h})
			}
		}
	}
	for _, v := range vs {
		prom := v.prom
		got := make(chan string, 2)
		check := func(where string, ss grpc.ServerStream) {
			if reflect.TypeOf(ss).Kind() != reflect.Pointer {
				got <- fmt.Sprintf("%s: %T is not a pointer", where, ss)
				return
			}
			// T-g (Q1): the interface value's data word is the pointer itself (Go stores a
			// pointer-typed dynamic value directly in the interface's second word).
			if w := (*[2]unsafe.Pointer)(unsafe.Pointer(&ss))[1]; w != reflect.ValueOf(ss).UnsafePointer() {
				got <- fmt.Sprintf("%s: %T's data word %p is not its pointer", where, ss, w)
				return
			}
			m := map[grpc.ServerStream]int{ss: 1}
			k := map[grpc.ServerStream]int{serverStreamWithCtx{ServerStream: ss, ctx: &cancellableContext{}}: 1}
			if m[ss] != 1 || len(k) != 1 {
				got <- where + ": map"
				return
			}
			got <- fmt.Sprintf("%s ok: %T", where, ss)
		}
		var ics []grpc.StreamServerInterceptor
		if prom {
			ics = append(ics, grpcprom.NewServerMetrics().StreamServerInterceptor())
		}
		// etcd's newStreamInterceptor's position: the last interceptor of the chain.
		ics = append(ics, func(srv any, ss grpc.ServerStream, info *grpc.StreamServerInfo, h grpc.StreamHandler) error {
			check("interceptor", ss)
			return h(srv, ss)
		})
		opts := []grpc.ServerOption{grpc.ChainStreamInterceptor(ics...)}
		if v.otel {
			opts = append(opts, grpc.StatsHandler(otelgrpc.NewServerHandler(
				otelgrpc.WithTracerProvider(sdktrace.NewTracerProvider()))))
		}
		start := startServer
		if v.http {
			start = startServerHTTP
		}
		cc := start(t, opts, func(_ any, ss grpc.ServerStream) error { check("handler", ss); return nil })
		runStream(t, cc, false)
		for i := 0; i < 2; i++ {
			s := <-got
			t.Logf("%+v: %s", v, s)
			if !strings.Contains(s, " ok: ") {
				t.Errorf("%+v: %s", v, s)
			}
		}
	}
}

// strictCtx: a WithCancel child whose Err() panics unless Done is closed, and returns
// ErrGRPCNoLeader once it is (as etcd's wrapper after its monitor's Cancel). It counts Err calls.
type strictCtx struct {
	context.Context
	errs atomic.Int32
}

func (c *strictCtx) Err() error {
	c.errs.Add(1)
	select {
	case <-c.Context.Done():
		return rpctypes.ErrGRPCNoLeader
	default:
		panic("Err() before Done")
	}
}

func TestRenewHTTPErrTiming(t *testing.T) {
	block := make(chan struct{})
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		if r.URL.Path == "/block" {
			select {
			case <-block:
			case <-r.Context().Done():
			}
			return
		}
		b, _ := proto.Marshal(&pb.LeaseKeepAliveResponse{ID: 7, TTL: 5})
		w.Header().Set("Content-Type", "application/protobuf")
		w.Write(b)
	}))
	defer srv.Close()
	defer close(block)
	rt := &http.Transport{}

	inner, cancel := context.WithCancel(context.Background())
	c := &strictCtx{Context: inner}
	ttl, err := leasehttp.RenewHTTP(c, lease.LeaseID(7), srv.URL+"/renew", rt)
	if err != nil || ttl != 5 {
		t.Fatalf("renew: %v %v", ttl, err)
	}
	t.Logf("success: Err() called %d times", c.errs.Load())

	done := make(chan error, 1)
	go func() {
		_, err := leasehttp.RenewHTTP(c, lease.LeaseID(7), srv.URL+"/block", rt)
		done <- err
	}()
	time.Sleep(200 * time.Millisecond)
	cancel()
	err = <-done
	if err == nil {
		t.Fatal("no error after cancel")
	}
	t.Logf("cancelled: %v (%T); Is(Canceled)=%v Is(ErrGRPCNoLeader)=%v; Err() called %d times",
		err, err, errors.Is(err, context.Canceled), errors.Is(err, rpctypes.ErrGRPCNoLeader), c.errs.Load())

	// Already cancelled when RenewHTTP is called (the M1 finding of the T-g review): the
	// transport's WithCancelCause(req.Context()) calls the caller's Err() synchronously, on the
	// caller's goroutine, in propagateCancel's already-done arm and in Cause (go1.27.3
	// context.go:487, 290). Err() is called, and the error returned is a non-nil *url.Error whose
	// Error() and errors.Is answer, as the spec's post (applyErrIs of every client error) has it.
	pre, cancelPre := context.WithCancel(context.Background())
	cancelPre()
	cp := &strictCtx{Context: pre}
	_, err = leasehttp.RenewHTTP(cp, lease.LeaseID(7), srv.URL+"/renew", rt)
	if err == nil {
		t.Fatal("pre-cancelled: no error")
	}
	var ue *url.Error
	if !errors.As(err, &ue) {
		t.Fatalf("pre-cancelled: %v (%T) is not a *url.Error", err, err)
	}
	if cp.errs.Load() == 0 {
		t.Fatal("pre-cancelled: Err() not called (the M1 claim no longer holds: update the notes)")
	}
	_ = err.Error()
	t.Logf("pre-cancelled: %v (%T); Is(ErrLeaseNotFound)=%v; Err() called %d times",
		err, err, errors.Is(err, lease.ErrLeaseNotFound), cp.errs.Load())
}

// spanOnlyCtx answers Value and panics on every other method (T-g, Q2).
type spanOnlyCtx struct{ v any }

func (spanOnlyCtx) Deadline() (time.Time, bool) { panic("Deadline called") }
func (spanOnlyCtx) Done() <-chan struct{}       { panic("Done called") }
func (spanOnlyCtx) Err() error                  { panic("Err called") }
func (c spanOnlyCtx) Value(key any) any         { return c.v }

// TestSpanFromContextValueOnly: otel's SpanFromContext reads only ctx.Value(currentSpanKey): a
// context whose Done, Err and Deadline panic works, answering nil (the no-op span) or a span.
func TestSpanFromContextValueOnly(t *testing.T) {
	sp := oteltrace.SpanFromContext(spanOnlyCtx{})
	if sp == nil || sp.SpanContext().IsValid() {
		t.Fatalf("nil value: got %v", sp)
	}
	sc := oteltrace.NewSpanContext(oteltrace.SpanContextConfig{TraceID: [16]byte{1}, SpanID: [8]byte{1}})
	want := oteltrace.SpanFromContext(oteltrace.ContextWithSpanContext(context.Background(), sc))
	got := oteltrace.SpanFromContext(spanOnlyCtx{v: want})
	if !got.SpanContext().Equal(want.SpanContext()) || !got.SpanContext().IsValid() {
		t.Fatalf("span value: got %v, want %v", got, want)
	}
}

// panicTraceCtx (T-h0): a context whose every method delegates to a real WithCancel child, except
// Value at net/http's httptrace key, which panics. It meets isContext's and srvCtxWeak's clauses
// (their Value clause speaks only of &cancelCtxKey).
type panicTraceCtx struct{ context.Context }

func (c panicTraceCtx) Value(k any) any {
	if fmt.Sprintf("%T", k) == "httptrace.clientEventContextKey" {
		panic("Value(httptrace key)")
	}
	return c.Context.Value(k)
}

// TestRenewHTTPValuePanics (T-h0, the refutation of RenewHTTP.spec as landed): RenewHTTP panics on
// such a context (net/http's Transport.roundTrip calls httptrace.ContextClientTrace(ctx)).
func TestRenewHTTPValuePanics(t *testing.T) {
	hs := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {}))
	defer hs.Close()
	inner, cancel := context.WithCancel(context.Background())
	defer cancel()
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("RenewHTTP did not panic (T-h0 no longer holds: update the notes)")
		}
		t.Logf("recovered: %v", r)
	}()
	leasehttp.RenewHTTP(panicTraceCtx{inner}, lease.LeaseID(1), hs.URL+"/leases", &http.Transport{})
}

type thKey struct{}

func newWrapper() *cancellableContext {
	inner, cancel := context.WithCancel(context.Background())
	return &cancellableContext{Context: inner, cancel: cancel}
}

// TestWithTimeoutWeak (T-h3): context.WithTimeout over etcd's wrapper (directly, and under a
// WithValue, Tracer.Start's link). Already cancelled with ErrGRPCNoLeader: the child is done, its
// Err() is ErrGRPCNoLeader (propagateCancel's already-done arm), not Canceled or DeadlineExceeded,
// and cancel() keeps it. Not yet done: the child registers with the wrapper's inner *cancelCtx, so
// the wrapper's Cancel(ErrGRPCNoLeader) gives it Canceled; its own timeout DeadlineExceeded, its
// cancel() Canceled.
func TestWithTimeoutWeak(t *testing.T) {
	for _, val := range []bool{false, true} {
		wrap := func(w *cancellableContext) context.Context {
			if val {
				return context.WithValue(w, thKey{}, 1)
			}
			return w
		}
		w := newWrapper()
		w.Cancel(rpctypes.ErrGRPCNoLeader)
		c, cancel := context.WithTimeout(wrap(w), time.Minute)
		<-c.Done()
		if c.Err() != rpctypes.ErrGRPCNoLeader || errors.Is(c.Err(), context.Canceled) ||
			errors.Is(c.Err(), context.DeadlineExceeded) {
			t.Fatalf("val=%v already done: %v", val, c.Err())
		}
		cancel()
		if c.Err() != rpctypes.ErrGRPCNoLeader {
			t.Fatalf("val=%v: cancel() changed Err to %v", val, c.Err())
		}
		w = newWrapper()
		c, cancel = context.WithTimeout(wrap(w), time.Minute)
		if c.Err() != nil {
			t.Fatalf("val=%v: Err before done: %v", val, c.Err())
		}
		w.Cancel(rpctypes.ErrGRPCNoLeader)
		<-c.Done()
		if c.Err() != context.Canceled {
			t.Fatalf("val=%v registered: %v", val, c.Err())
		}
		cancel()
		w = newWrapper()
		c, cancel = context.WithTimeout(wrap(w), time.Millisecond)
		<-c.Done()
		if c.Err() != context.DeadlineExceeded {
			t.Fatalf("val=%v timeout: %v", val, c.Err())
		}
		cancel()
		w = newWrapper()
		c, cancel = context.WithTimeout(wrap(w), time.Minute)
		cancel()
		if c.Err() != context.Canceled {
			t.Fatalf("val=%v cancel: %v", val, c.Err())
		}
	}
}

// TestNoLeaderTyped (T-h2): ErrGRPCNoLeader is a *status.Error, an error.
func TestNoLeaderTyped(t *testing.T) {
	var a any = rpctypes.ErrGRPCNoLeader
	e, ok := a.(error)
	if !ok || e == nil {
		t.Fatal("ErrGRPCNoLeader is not an error")
	}
	if got := fmt.Sprintf("%T", e); got != "*status.Error" {
		t.Fatalf("dynamic type %s", got)
	}
}

// nilCancelCtx (T-h5): a context whose every method delegates to a real WithCancel child, except
// Value at context's own &cancelCtxKey, where it returns a nil pointer of the dynamic type the
// child returns (*context.cancelCtx, built by reflect: the type is unexported). Value(&cancelCtxKey)
// returns, with no fact of the value: what T-h2's ctxDoneErr "#HValueAny" admits.
type nilCancelCtx struct{ context.Context }

func (c nilCancelCtx) Value(k any) any {
	v := c.Context.Value(k)
	if fmt.Sprintf("%T", v) == "*context.cancelCtx" {
		return reflect.Zero(reflect.TypeOf(v)).Interface()
	}
	return v
}

// TestRenewHTTPNilCancelCtxPanics (T-h5): RenewHTTP panics on such a context: net/http's
// WithCancelCause(req.Context()) calls propagateCancel, whose parentCancelCtx asserts the value to
// *cancelCtx (ok) and loads its done field through the nil pointer (go1.27.3 context.go:403-411).
func TestRenewHTTPNilCancelCtxPanics(t *testing.T) {
	hs := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {}))
	defer hs.Close()
	inner, cancel := context.WithCancel(context.Background())
	defer cancel()
	defer func() {
		r := recover()
		if r == nil {
			t.Fatal("RenewHTTP did not panic (T-h5 no longer holds: update the notes)")
		}
		t.Logf("recovered: %v", r)
	}()
	leasehttp.RenewHTTP(nilCancelCtx{inner}, lease.LeaseID(1), hs.URL+"/leases", &http.Transport{})
}
