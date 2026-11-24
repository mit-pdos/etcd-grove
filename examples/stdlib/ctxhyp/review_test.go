// The adversarial review's checks (notes/axiom-review/context-interim-hypotheses.md, 2026-11-24) of context.WithValue.specPtr and context.WithCancel.specValBg (go1.27.3).
package ctxhyp

import (
	"context"
	"errors"
	"fmt"
	"reflect"
	"runtime"
	"sync"
	"testing"
	"time"
	"unsafe"
)

type zs struct{}
type P *int // a named pointer type: its dynamic type is P (Named), outside specPtr's PointerType premise

func rfield(p any, i int) any {
	v := reflect.ValueOf(p).Elem()
	f := v.Field(i)
	return reflect.NewAt(f.Type(), unsafe.Pointer(f.UnsafeAddr())).Elem().Interface()
}

func rchain(n int) context.Context {
	c := context.Background()
	for i := 0; i < n; i++ {
		c = context.WithValue(c, new(int), i)
	}
	return c
}

// 1. specPtr: odd pointer keys, typed-nil parents, non-comparable vals: no panic, a *valueCtx.
func TestWithValueOddPointerKeys(t *testing.T) {
	var nilCancel context.Context = (*struct{ context.Context })(nil) // non-nil interface, nil pointer
	keys := []any{new(zs), (*zs)(nil), new(func()), new(map[int]int), new([]int), new(any), new(*int),
		(*[0]int)(nil), new(chan int), new(unsafe.Pointer), new(error)}
	vals := []any{nil, []int{1}, map[int]int{}, func() {}}
	for _, parent := range []context.Context{context.Background(), context.TODO(), nilCancel, rchain(3)} {
		for _, k := range keys {
			for _, v := range vals {
				c := context.WithValue(parent, k, v)
				if fmt.Sprintf("%T", c) != "*context.valueCtx" {
					t.Fatalf("%T", c)
				}
				if rfield(c, 0) != parent || rfield(c, 1) != k {
					t.Fatal("fields")
				}
			}
		}
	}
	// named pointer type: also fine in Go (spec says nothing of it).
	_ = context.WithValue(context.Background(), P(nil), 1)
}

// 2. Zero-size pointer keys alias in gc: Go's == on two distinct new(zs) may be true. specPtr
// says nothing about key equality, but Perennial's ctxValue_valueCtx law (keyEqOk) does.
func TestZeroSizeKeyAlias(t *testing.T) {
	k1, k2 := new(zs), new(zs)
	runtime.KeepAlive(fmt.Sprint(k1, k2)) // make both escape
	c := context.WithValue(context.Background(), k1, "x")
	t.Logf("k1==k2: %v; c.Value(k2)=%v", k1 == k2, c.Value(k2))
}

// 3. specValBg under concurrency: cancel many times concurrently with Done/Err/Deadline/Cause, and
// children (WithCancel, WithTimeout, AfterFunc, WithoutCancel) of ctx'. Run with -race.
func TestWithCancelChainConcurrent(t *testing.T) {
	for depth := 0; depth < 6; depth++ {
		for iter := 0; iter < 200; iter++ {
			before := runtime.NumGoroutine()
			parent := rchain(depth)
			if parent.Done() != nil {
				t.Fatal("chain Done not nil")
			}
			ctx, cancel := context.WithCancel(parent)
			if runtime.NumGoroutine() != before {
				t.Fatal("goroutine started")
			}
			if fmt.Sprintf("%T", ctx) != "*context.cancelCtx" {
				t.Fatal("type")
			}
			if d, ok := ctx.Deadline(); ok || !d.IsZero() {
				t.Fatal("deadline")
			}
			child, ccancel := context.WithCancel(ctx)
			tchild, tcancel := context.WithTimeout(ctx, time.Hour)
			fired := make(chan struct{})
			stop := context.AfterFunc(ctx, func() { close(fired) })
			_ = stop
			var wg sync.WaitGroup
			for g := 0; g < 4; g++ {
				wg.Add(1)
				go func() {
					defer wg.Done()
					<-ctx.Done()
					if !errors.Is(ctx.Err(), context.Canceled) || ctx.Err() != context.Canceled {
						panic("err")
					}
					if context.Cause(ctx) != context.Canceled {
						panic("cause")
					}
				}()
				wg.Add(1)
				go func() { defer wg.Done(); _ = ctx.Err(); _, _ = ctx.Deadline(); cancel() }()
			}
			wg.Wait()
			<-child.Done()
			<-tchild.Done()
			<-fired
			if tchild.Err() != context.Canceled {
				t.Fatal("timer child err", tchild.Err())
			}
			ccancel()
			tcancel()
			cancel()
			if parent.Done() != nil || parent.Err() != nil {
				t.Fatal("parent changed")
			}
		}
	}
}

// 4. Err before cancel is nil, Done is the same channel each time, Done closed after cancel.
func TestWithCancelChainSequential(t *testing.T) {
	ctx, cancel := context.WithCancel(rchain(4))
	if ctx.Err() != nil {
		t.Fatal()
	}
	d1, d2 := ctx.Done(), ctx.Done()
	if d1 != d2 || d1 == nil {
		t.Fatal()
	}
	select {
	case <-d1:
		t.Fatal("closed early")
	default:
	}
	cancel()
	<-d1
	// cancel before Done: closedchan path
	ctx2, cancel2 := context.WithCancel(rchain(2))
	cancel2()
	<-ctx2.Done()
	if ctx2.Err() != context.Canceled {
		t.Fatal()
	}
	cancel2()
}

// 5. Deep chain (stack): WithCancel walks Done recursively.
func TestDeepChain(t *testing.T) {
	ctx, cancel := context.WithCancel(rchain(100000))
	cancel()
	<-ctx.Done()
}

// 6. The valueCtx's key/val are unexported (CanSet false), but its embedded field `Context` is
// EXPORTED (an embedded field takes its type's name, `Context`), so reflection outside the context
// package can write it: the docstring's "they are unexported" is wrong for that field. Writing a nil
// Context then makes WithCancel(chain) panic (nil-interface method call in propagateCancel's
// parent.Done()). Not a counterexample to the triple: Perennial's reflect has no Field spec and the
// repo's Value.Set spec needs full ownership `p ↦ x`, which ↦□ never yields.
func TestReflectWritesEmbeddedContext(t *testing.T) {
	c := context.WithValue(context.Background(), new(int), 1)
	v := reflect.ValueOf(c).Elem()
	for i := 0; i < v.NumField(); i++ {
		t.Logf("field %d %s CanSet=%v", i, v.Type().Field(i).Name, v.Field(i).CanSet())
	}
	if v.Field(1).CanSet() || v.Field(2).CanSet() {
		t.Fatal("key/val settable")
	}
	if !v.Field(0).CanSet() {
		t.Fatal("Context field expected settable")
	}
	v.Field(0).Set(reflect.Zero(v.Field(0).Type()))
	defer func() {
		r := recover()
		t.Logf("WithCancel after the reflective write: recovered %v", r)
		if r == nil {
			t.Fatal("expected a panic")
		}
	}()
	_, cf := context.WithCancel(c)
	cf()
}
