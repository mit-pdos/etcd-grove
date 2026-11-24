// Package ctxhyp is the Go evidence (go1.27.3 linux/amd64) for two interim pending hypotheses on
// `context` that net/http's server proofs take (`Net/Proof/net/http/Results.lean`):
//   - context.WithValue.specPtr (Net/Spec/context/WithValuePtr.lean): WithValue of a non-nil parent
//     and a key of pointer type returns a fresh *valueCtx holding (parent, key, val), whose fields
//     are never written by `context` (TestWithValuePtrKey, TestWithValueExcluded,
//     TestValueCtxFieldsNeverWritten, TestNetHTTPChain; review: TestWithValueOddPointerKeys,
//     TestZeroSizeKeyAlias, TestReflectWritesEmbeddedContext: only reflection, from outside, can
//     write the exported embedded field Context, which needs ownership the spec's ↦□ excludes);
//   - context.WithCancel.specValBg (Net/Spec/context/WithCancelValBg.lean): WithCancel of
//     Background() or a *valueCtx chain over it behaves as WithCancel(Background()) does
//     (TestWithCancelValBg, TestNetHTTPChain; review: TestWithCancelChainConcurrent,
//     TestWithCancelChainSequential, TestDeepChain).
//
// review_test.go holds the independent adversarial review's tests (both hypotheses sound, no
// counterexample: notes/axiom-review/context-interim-hypotheses.md, summarized in notes/perennial-changes.md).
// Run: GOTOOLCHAIN=go1.27.3 go test -race -count=1 ./stdlib/ctxhyp/ (in examples/).
package ctxhyp

import (
	"context"
	"errors"
	"fmt"
	"net"
	"net/http"
	"reflect"
	"runtime"
	"testing"
	"time"
	"unsafe"
)

// field reads struct field i of the struct *p points to, exported or not.
func field(p any, i int) any {
	v := reflect.ValueOf(p).Elem()
	f := v.Field(i)
	return reflect.NewAt(f.Type(), unsafe.Pointer(f.UnsafeAddr())).Elem().Interface()
}

func fieldName(p any, i int) string { return reflect.ValueOf(p).Elem().Type().Field(i).Name }

func ptr(p any) uintptr { return reflect.ValueOf(p).Pointer() }

// checkValueCtx: ctx is a *context.valueCtx whose fields (Context, key, val) are parent, key, val.
func checkValueCtx(t *testing.T, ctx, parent, key, val any) {
	t.Helper()
	if got := fmt.Sprintf("%T", ctx); got != "*context.valueCtx" {
		t.Fatalf("dynamic type %s, want *context.valueCtx", got)
	}
	if n := reflect.ValueOf(ctx).Elem().NumField(); n != 3 {
		t.Fatalf("valueCtx has %d fields, want 3", n)
	}
	for i, w := range []string{"Context", "key", "val"} {
		if fieldName(ctx, i) != w {
			t.Fatalf("field %d is %s, want %s", i, fieldName(ctx, i), w)
		}
	}
	if field(ctx, 0) != parent {
		t.Fatalf("Context field %v, want the parent %v", field(ctx, 0), parent)
	}
	if field(ctx, 1) != key {
		t.Fatalf("key field %v, want %v", field(ctx, 1), key)
	}
	if !reflect.DeepEqual(field(ctx, 2), val) || (val != nil && reflect.TypeOf(val).Comparable() && field(ctx, 2) != val) {
		t.Fatalf("val field %v, want %v", field(ctx, 2), val)
	}
}

type big struct{ a [64]byte }

// WithValue.specPtr: any non-nil parent, any pointer key (nil pointer, pointer to a
// non-comparable type included), any val (nil included): no panic, a fresh *valueCtx holding
// exactly (parent, key, val).
func TestWithValuePtrKey(t *testing.T) {
	var x int
	var sl []int
	var m map[int]int
	var f func()
	keys := []any{
		http.ServerContextKey, http.LocalAddrContextKey, // what net/http's Serve and conn.serve pass
		&x, (*int)(nil), &sl, &m, &f, (*[]int)(nil), &big{}, (*struct{})(nil),
	}
	cctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	parents := []context.Context{context.Background(), context.TODO(), cctx,
		context.WithValue(context.Background(), &x, 1)}
	vals := []any{nil, 1, "s", &x, []int{1}, (*int)(nil), &http.Server{}}
	for _, p := range parents {
		for _, k := range keys {
			for _, v := range vals {
				c1 := context.WithValue(p, k, v)
				checkValueCtx(t, c1, p, k, v)
				c2 := context.WithValue(p, k, v)
				if ptr(c1) == ptr(c2) || ptr(c1) == 0 {
					t.Fatalf("WithValue results not fresh: %x %x", ptr(c1), ptr(c2))
				}
			}
		}
	}
}

// The checks WithValue does: these are what the spec's premises exclude (a non-nil parent, a
// non-nil key of pointer type). Each panics in Go.
func TestWithValueExcluded(t *testing.T) {
	mustPanic := func(name, want string, f func()) {
		t.Helper()
		defer func() {
			r := recover()
			if r == nil || fmt.Sprint(r) != want {
				t.Fatalf("%s: recovered %v, want panic %q", name, r, want)
			}
		}()
		f()
	}
	var x int
	mustPanic("nil parent", "cannot create context from nil parent", func() { _ = context.WithValue(nil, &x, 1) })
	mustPanic("nil key", "nil key", func() { _ = context.WithValue(context.Background(), nil, 1) })
	mustPanic("slice key", "key is not comparable", func() { _ = context.WithValue(context.Background(), []int{}, 1) })
}

// chain builds n *valueCtx over Background(), keys of several types (pointers, as net/http's,
// and other comparable keys: the hypothesis's ctxBg admits any key).
func chain(n int) context.Context {
	var c context.Context = context.Background()
	keys := []any{http.ServerContextKey, http.LocalAddrContextKey, "k", 7, new(int), struct{}{}}
	for i := 0; i < n; i++ {
		c = context.WithValue(c, keys[i%len(keys)], i)
	}
	return c
}

// WithCancel.specValBg: for Background() or a *valueCtx chain over it, WithCancel returns a
// *cancelCtx whose parent is the chain, whose Deadline is (zero, false), whose Done channel is
// open and Err nil until its cancel function runs, after which Done is closed and Err is
// Canceled (cancel needs nothing, may run any number of times); it starts no goroutine and
// changes nothing of the chain; the new context is a parent *cancelCtx for WithCancel.
func TestWithCancelValBg(t *testing.T) {
	for n := 0; n <= 8; n++ {
		parent := chain(n)
		if parent.Done() != nil {
			t.Fatalf("n=%d: chain's Done() not nil", n)
		}
		var before []any
		for q, i := parent, 0; i < n; i++ {
			before = append(before, field(q, 0), field(q, 1), field(q, 2))
			q = field(q, 0).(context.Context)
		}
		g0 := runtime.NumGoroutine()
		ctx, cancel := context.WithCancel(parent)
		if got := fmt.Sprintf("%T", ctx); got != "*context.cancelCtx" {
			t.Fatalf("n=%d: dynamic type %s, want *context.cancelCtx", n, got)
		}
		if field(ctx, 0) != parent {
			t.Fatalf("n=%d: cancelCtx's Context is not the parent", n)
		}
		if g := runtime.NumGoroutine(); g != g0 {
			t.Fatalf("n=%d: WithCancel started goroutines (%d -> %d)", n, g0, g)
		}
		if d, ok := ctx.Deadline(); ok || !d.Equal(time.Time{}) {
			t.Fatalf("n=%d: Deadline %v %v", n, d, ok)
		}
		done := ctx.Done()
		if done == nil {
			t.Fatalf("n=%d: Done nil", n)
		}
		select {
		case <-done:
			t.Fatalf("n=%d: done before cancel", n)
		default:
		}
		if ctx.Err() != nil {
			t.Fatalf("n=%d: Err before cancel", n)
		}
		// A child of ctx registers with it (ctx is a parent *cancelCtx).
		child, ccancel := context.WithCancel(ctx)
		defer ccancel()
		if g := runtime.NumGoroutine(); g != g0 {
			t.Fatalf("n=%d: child's WithCancel started goroutines", n)
		}
		cancel()
		cancel()
		select {
		case <-done:
		default:
			t.Fatalf("n=%d: Done not closed after cancel", n)
		}
		if ctx.Done() != done {
			t.Fatalf("n=%d: Done changed", n)
		}
		if !errors.Is(ctx.Err(), context.Canceled) || ctx.Err() != context.Canceled {
			t.Fatalf("n=%d: Err %v after cancel", n, ctx.Err())
		}
		<-child.Done()
		if parent.Err() != nil || parent.Done() != nil {
			t.Fatalf("n=%d: parent affected", n)
		}
		var after []any
		for q, i := parent, 0; i < n; i++ {
			after = append(after, field(q, 0), field(q, 1), field(q, 2))
			q = field(q, 0).(context.Context)
		}
		if !reflect.DeepEqual(before, after) {
			t.Fatalf("n=%d: chain changed", n)
		}
	}
}

// net/http's own use: Serve's context and conn.serve's, the exact chain the proof takes.
func TestNetHTTPChain(t *testing.T) {
	srv := &http.Server{}
	la := &net.TCPAddr{IP: net.IPv4(127, 0, 0, 1), Port: 1}
	base := context.Background()
	c1 := context.WithValue(base, http.ServerContextKey, srv)
	checkValueCtx(t, c1, base, http.ServerContextKey, srv)
	c2 := context.WithValue(c1, http.LocalAddrContextKey, net.Addr(la))
	checkValueCtx(t, c2, c1, http.LocalAddrContextKey, net.Addr(la))
	ctx, cancel := context.WithCancel(c2)
	if fmt.Sprintf("%T", ctx) != "*context.cancelCtx" || field(ctx, 0) != context.Context(c2) {
		t.Fatalf("WithCancel of the chain: %T", ctx)
	}
	cancel()
	if ctx.Err() != context.Canceled {
		t.Fatalf("Err %v", ctx.Err())
	}
}
