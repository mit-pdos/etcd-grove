// Package streamctx checks the claims of the trusted texts of k8s 7f-4 (notes/k8s-7f4-freeze.md §2)
// about grpc's stream handler contexts and the specs a require-leader stream handler's context
// reaches, at the pins (grpc v1.84.0, go-grpc-middleware v2.3.4 / providers/prometheus v1.1.0,
// otelgrpc v0.71.0, etcd's fork):
//
//   - T-a (TestRunCtxChain): the context a stream handler's ServerStream returns is a chain of
//     *context.valueCtx, *context.cancelCtx and *context.timerCtx links over Background(), which
//     context.value() walks, so the chain form of its library values (ctxValue) holds; with and
//     without TLS, otelgrpc's stats handler, a client deadline and grpc-prometheus's interceptor.
//   - T-b, as revised (TestIncomingOfValue; Revision 1 of the freeze note, B1): a *cancelCtx has
//     its parent's incoming metadata (metadata.incomingOf_cancelCtx), and etcd's require-leader
//     wrapper (*cancellableContext) its embedded context's (v3rpc.incomingOf_cancellableContext),
//     after its Cancel(ErrGRPCNoLeader) too; also a context whose Done, Err and Deadline panic and a
//     WithValue child. metadata.FromIncomingContext reads only Value(mdIncomingKey{}).
//   - T-c (TestRawStreamKey): the ServerStream an interceptor or handler receives is a pointer (grpc's
//     *serverStream, prometheus's *monitoredServerStream), a comparable map key, alone or in a
//     struct beside a pointer (etcd's serverStreamWithCtx).
//   - T-f (TestRenewHTTPErrTiming): leasehttp.RenewHTTP over a *http.Transport calls the context's
//     Err() only once Done is closed (a context whose Err panics before Done is fine), and returns
//     an error when it is cancelled with an Err() of ErrGRPCNoLeader.
package streamctx

import (
	"context"
	"errors"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/http/httptest"
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
	oteltrace "go.opentelemetry.io/otel/trace"
	sdktrace "go.opentelemetry.io/otel/sdk/trace"
	"google.golang.org/grpc"
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

var chainTys = map[string]bool{"*context.valueCtx": true, "*context.cancelCtx": true,
	"*context.timerCtx": true, "context.backgroundCtx": true}

func TestRunCtxChain(t *testing.T) {
	for _, prom := range []bool{false, true} {
		for _, otel := range []bool{false, true} {
			for _, dl := range []bool{false, true} {
				name := fmt.Sprintf("prom=%v otel=%v deadline=%v", prom, otel, dl)
				var opts []grpc.ServerOption
				if prom {
					opts = append(opts, grpc.ChainStreamInterceptor(grpcprom.NewServerMetrics().StreamServerInterceptor()))
				}
				if otel {
					opts = append(opts, grpc.StatsHandler(otelgrpc.NewServerHandler(
						otelgrpc.WithTracerProvider(sdktrace.NewTracerProvider()))))
				}
				got := make(chan []string, 1)
				cc := startServer(t, opts, func(_ any, ss grpc.ServerStream) error {
					got <- chain(ss.Context())
					return nil
				})
				runStream(t, cc, dl)
				tys := <-got
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

func TestRawStreamKey(t *testing.T) {
	for _, prom := range []bool{false, true} {
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
		cc := startServer(t, []grpc.ServerOption{grpc.ChainStreamInterceptor(ics...)},
			func(_ any, ss grpc.ServerStream) error { check("handler", ss); return nil })
		runStream(t, cc, false)
		for i := 0; i < 2; i++ {
			s := <-got
			t.Logf("prom=%v: %s", prom, s)
			if !strings.Contains(s, " ok: ") {
				t.Errorf("prom=%v: %s", prom, s)
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
