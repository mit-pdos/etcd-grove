package ctxvalue

import (
	"context"
	"testing"
	"time"

	"google.golang.org/grpc"
	"google.golang.org/protobuf/types/known/emptypb"
)

// quietDeadlinePanic: Done nil, Err nil, Value nil (ctxQuiet holds), Deadline panics.
type quietDeadlinePanic struct{}

func (quietDeadlinePanic) Deadline() (time.Time, bool) { panic("Deadline") }
func (quietDeadlinePanic) Done() <-chan struct{}       { return nil }
func (quietDeadlinePanic) Err() error                  { return nil }
func (quietDeadlinePanic) Value(any) any               { return nil }

// errsCancelKeyPanic: Done a never-closed channel, Err nil (ctxErrs at a never-done descriptor),
// Deadline fine, Value nil except at a *int key (&cancelCtxKey), where it panics.
type errsCancelKeyPanic struct{ ch chan struct{} }

func (errsCancelKeyPanic) Deadline() (time.Time, bool) { return time.Time{}, false }
func (c errsCancelKeyPanic) Done() <-chan struct{}     { return c.ch }
func (errsCancelKeyPanic) Err() error                  { return nil }
func (errsCancelKeyPanic) Value(k any) any {
	if _, ok := k.(*int); ok {
		panic("Value(&cancelCtxKey)")
	}
	return nil
}

// quietValuePanic: ctxQuiet holds (Done nil, Err nil), Deadline fine, Value panics.
type quietValuePanic struct{}

func (quietValuePanic) Deadline() (time.Time, bool) { return time.Time{}, false }
func (quietValuePanic) Done() <-chan struct{}       { return nil }
func (quietValuePanic) Err() error                  { return nil }
func (quietValuePanic) Value(any) any               { panic("Value") }

func TestScratchInvokeCtx(t *testing.T) {
	unary := func(_ any, ctx context.Context, dec func(any) error, _ grpc.UnaryServerInterceptor) (any, error) {
		in := new(emptypb.Empty)
		if err := dec(in); err != nil {
			return nil, err
		}
		return new(emptypb.Empty), nil
	}
	stream := func(any, grpc.ServerStream) error { return nil }
	cc := startServer(t, false, nil, unary, stream)
	// warm up
	if err := cc.Invoke(context.Background(), "/t.S/U", new(emptypb.Empty), new(emptypb.Empty)); err != nil {
		t.Fatal(err)
	}
	for name, ctx := range map[string]context.Context{
		"quietDeadlinePanic": quietDeadlinePanic{},
		"errsCancelKeyPanic": errsCancelKeyPanic{ch: make(chan struct{})},
		"quietValuePanic":    quietValuePanic{},
	} {
		p := panics(func() { _ = cc.Invoke(ctx, "/t.S/U", new(emptypb.Empty), new(emptypb.Empty)) })
		ps := panics(func() { _, _ = cc.NewStream(ctx, &streamDesc, "/t.S/S") })
		t.Logf("%s: Invoke panics=%v NewStream panics=%v", name, p, ps)
	}
}

// errsAfterFuncPanic: as errsCancelKeyPanic but Value nil everywhere, and an AfterFunc method that panics.
type errsAfterFuncPanic struct{ ch chan struct{} }

func (errsAfterFuncPanic) Deadline() (time.Time, bool)   { return time.Time{}, false }
func (c errsAfterFuncPanic) Done() <-chan struct{}       { return c.ch }
func (errsAfterFuncPanic) Err() error                    { return nil }
func (errsAfterFuncPanic) Value(any) any                 { return nil }
func (errsAfterFuncPanic) AfterFunc(func()) func() bool  { panic("AfterFunc") }

func TestScratchAfterFunc(t *testing.T) {
	unary := func(_ any, ctx context.Context, dec func(any) error, _ grpc.UnaryServerInterceptor) (any, error) {
		in := new(emptypb.Empty)
		if err := dec(in); err != nil {
			return nil, err
		}
		return new(emptypb.Empty), nil
	}
	cc := startServer(t, false, nil, unary, func(any, grpc.ServerStream) error { return nil })
	ctx := errsAfterFuncPanic{ch: make(chan struct{})}
	p := panics(func() { _ = cc.Invoke(ctx, "/t.S/U", new(emptypb.Empty), new(emptypb.Empty)) })
	t.Logf("errsAfterFuncPanic: Invoke panics=%v", p)
}
