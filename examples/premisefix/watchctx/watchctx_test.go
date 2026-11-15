// Package watchctx checks the premise of context.WithCancelValCtx.spec and watcher.Watch.spec,
// EtcdGrove.context.watchCtx (Proof/context/WatchCtx.lean), at the pins (go1.27.3, grpc v1.84.0,
// etcd's fork): the context sweep's fixes (2026-11-13, notes/ctx-sweep-fixes.md).
//
// The client's Watch runs context.WithCancel(&valCtx{ctx}) (client/v3/watch.go,
// newWatcherGRPCStream) on the caller's goroutine. valCtx overrides Deadline, Done (the never-closed
// valCtxCh) and Err, and promotes ctx's Value. Go's propagateCancel, the parent's Done() being not
// nil, calls parentCancelCtx(&valCtx{ctx}), which calls ctx.Value(&cancelCtxKey) and, if the result
// is a *cancelCtx, dereferences it (go1.27.3 context.go:388-392). Until the fix watchCtx stated
// Done(), Err() and Value(mdOutgoingKey{}) only:
//
//   - TestWithCancelValCtxPanics: a context whose Value panics at &cancelCtxKey (an *int) met it, and
//     Watch panics;
//   - TestWithCancelValCtxTypedNil: so did one whose Value(&cancelCtxKey) is a typed-nil
//     *context.cancelCtx, and Watch panics with a nil dereference.
//
// The new clause ("#HCC", isContext's "#HValue": Value(&cancelCtxKey) returns, and a *cancelCtx it
// returns is a valid one) rules both out. TestWatchControl: a context meeting it (Value(&cancelCtxKey)
// nil, as a channelContext's; or a real *cancelCtx, as an isContext's), panicking at every other key
// but grpc's outgoing metadata, does not make Watch panic: its client path reads no other key.
package watchctx

import (
	"context"
	"fmt"
	"net"
	"reflect"
	"strings"
	"testing"
	"time"

	clientv3 "go.etcd.io/etcd/client/v3"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

// recCtx records every Value key and panics on the keys not in allow (by type name).
type recCtx struct {
	context.Context
	allow      map[string]bool
	seen       *[]string
	nilCC      bool // Value(&cancelCtxKey) is nil
	passCC     bool // Value(&cancelCtxKey) is the embedded context's (a real *cancelCtx)
	typedNilCC bool // Value(&cancelCtxKey) is a typed-nil *context.cancelCtx
}

func keyName(k any) string { return reflect.TypeOf(k).String() }

func (c *recCtx) Value(k any) any {
	n := keyName(k)
	*c.seen = append(*c.seen, n)
	if n == "*int" { // &cancelCtxKey is an *int
		switch {
		case c.typedNilCC:
			cc, cancel := context.WithCancel(context.Background())
			defer cancel()
			return reflect.Zero(reflect.TypeOf(cc.Value(k))).Interface() // (*context.cancelCtx)(nil)
		case c.nilCC:
			return nil
		case c.passCC:
			return c.Context.Value(k)
		}
	}
	if c.allow[n] {
		return c.Context.Value(k)
	}
	panic("Value at unconstrained key " + n)
}

func server(t *testing.T) string {
	lis, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	s := grpc.NewServer(grpc.UnknownServiceHandler(func(srv any, ss grpc.ServerStream) error {
		return status.Error(codes.Internal, "test handler")
	}))
	go s.Serve(lis)
	t.Cleanup(s.Stop)
	return lis.Addr().String()
}

func client(t *testing.T) *clientv3.Client {
	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{server(t)}, DialTimeout: 2 * time.Second})
	if err != nil {
		t.Fatal(err)
	}
	return cli
}

func run(f func()) (panicked any) {
	defer func() { panicked = recover() }()
	f()
	return nil
}

var grpcOnly = map[string]bool{"metadata.mdOutgoingKey": true}

func uniq(s []string) []string {
	m := map[string]bool{}
	var out []string
	for _, x := range s {
		if !m[x] {
			m[x] = true
			out = append(out, x)
		}
	}
	return out
}

func TestWithCancelValCtxPanics(t *testing.T) {
	cli := client(t) // no cli.Close: the panic leaves the watcher's mutex held
	var seen []string
	base, cancel := context.WithCancel(context.Background())
	defer cancel()
	ctx := &recCtx{Context: base, allow: grpcOnly, seen: &seen}
	p := run(func() { cli.Watch(ctx, "a") })
	t.Logf("Watch panic=%v keys=%v", p, uniq(seen))
	if p == nil || !strings.Contains(fmt.Sprint(p), "*int") {
		t.Fatalf("expected a panic at &cancelCtxKey, got %v", p)
	}
}

func TestWithCancelValCtxTypedNil(t *testing.T) {
	cli := client(t)
	var seen []string
	base, cancel := context.WithCancel(context.Background())
	defer cancel()
	ctx := &recCtx{Context: base, allow: grpcOnly, seen: &seen, typedNilCC: true}
	p := run(func() { cli.Watch(ctx, "a") })
	t.Logf("Watch typed-nil panic=%v keys=%v", p, uniq(seen))
	if p == nil || !strings.Contains(fmt.Sprint(p), "nil pointer") {
		t.Fatalf("expected a nil dereference, got %v", p)
	}
}

func TestWatchControl(t *testing.T) {
	for name, mk := range map[string]func(base context.Context, seen *[]string) *recCtx{
		"nil":       func(b context.Context, s *[]string) *recCtx { return &recCtx{Context: b, allow: grpcOnly, seen: s, nilCC: true} },
		"cancelCtx": func(b context.Context, s *[]string) *recCtx { return &recCtx{Context: b, allow: grpcOnly, seen: s, passCC: true} },
	} {
		t.Run(name, func(t *testing.T) {
			cli := client(t)
			defer cli.Close()
			var seen []string
			base, cancel := context.WithCancel(context.Background())
			ctx := mk(base, &seen)
			done := make(chan any)
			go func() { done <- run(func() { for range cli.Watch(ctx, "a") {} }) }()
			time.Sleep(1500 * time.Millisecond)
			cancel()
			p := <-done
			t.Logf("Watch control panic=%v keys=%v", p, uniq(seen))
			if p != nil {
				t.Errorf("panic: %v", p)
			}
		})
	}
}
