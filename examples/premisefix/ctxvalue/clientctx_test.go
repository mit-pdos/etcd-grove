package ctxvalue

// premise-fixes-8, part C (Scope: /shared/tmp/premise-fixes-8/scope.md, §0 and §4).
//
// grpc's client reads more of a call's context than ctxOk's arms (ctxQuiet, ctxErrs) state:
// newClientStreamWithParams runs context.WithCancel or WithTimeout on it, the transport calls
// Deadline() on the child (which delegates to the parent), and Go's propagateCancel, once Done()
// is not nil, calls parent.Value(&cancelCtxKey) and parent.AfterFunc if the type has it. So
// Invoke and NewStream panic on a context meeting ctxQuiet whose Value or Deadline panics (item 3,
// N1), on one meeting ctxErrs whose Value panics at a *int key (N2), or whose AfterFunc panics
// (N3); clientv3's withVersion reads FromOutgoingContext itself (TestClientCallCtxPanics). The
// fix (C1-C3): ctxOk carries metadata.outgoingCtxOkC (Proof/context/LibKeysChain.lean), both arms
// a Deadline clause, ctxErrs a *int-key Value clause and no AfterFunc. TestClientContexts checks
// those facts on the contexts the client builds and the closed programs pass.

import (
	"context"
	"reflect"
	"strings"
	"testing"
	"time"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	"go.etcd.io/etcd/api/v3/version"
	clientv3 "go.etcd.io/etcd/client/v3"
	"google.golang.org/grpc"
	"google.golang.org/grpc/metadata"
	"google.golang.org/protobuf/types/known/emptypb"
)

// quietDeadlinePanic: Done nil, Err nil, Value nil (ctxQuiet holds), Deadline panics (N1).
type quietDeadlinePanic struct{}

func (quietDeadlinePanic) Deadline() (time.Time, bool) { panic("Deadline") }
func (quietDeadlinePanic) Done() <-chan struct{}       { return nil }
func (quietDeadlinePanic) Err() error                  { return nil }
func (quietDeadlinePanic) Value(any) any               { return nil }

// quietValuePanic: ctxQuiet holds (Done nil, Err nil), Deadline fine, Value panics (item 3).
type quietValuePanic struct{}

func (quietValuePanic) Deadline() (time.Time, bool) { return time.Time{}, false }
func (quietValuePanic) Done() <-chan struct{}       { return nil }
func (quietValuePanic) Err() error                  { return nil }
func (quietValuePanic) Value(any) any               { panic("Value") }

// errsCancelKeyPanic: Done a never-closed channel, Err nil (ctxErrs at a never-done descriptor),
// Deadline fine, Value nil except at a *int key (&cancelCtxKey), where it panics (N2).
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

// errsNilCancelCtx: as errsCancelKeyPanic, but Value returns, at a *int key, a nil *cancelCtx
// (reflect.Zero of a real one's type): Value returns, yet parentCancelCtx dereferences it. So the
// clause must say that Value(&cancelCtxKey) is not a *cancelCtx, not only that it returns.
type errsNilCancelCtx struct{ ch chan struct{} }

var nilCancelCtx = func() any {
	c, cancel := context.WithCancel(context.Background())
	defer cancel()
	return reflect.Zero(reflect.TypeOf(c)).Interface()
}()

func (errsNilCancelCtx) Deadline() (time.Time, bool) { return time.Time{}, false }
func (c errsNilCancelCtx) Done() <-chan struct{}     { return c.ch }
func (errsNilCancelCtx) Err() error                  { return nil }
func (errsNilCancelCtx) Value(k any) any {
	if _, ok := k.(*int); ok {
		return nilCancelCtx
	}
	return nil
}

// errsAfterFuncPanic: as errsCancelKeyPanic but Value nil everywhere, and an AfterFunc method that
// panics (N3).
type errsAfterFuncPanic struct{ ch chan struct{} }

func (errsAfterFuncPanic) Deadline() (time.Time, bool)  { return time.Time{}, false }
func (c errsAfterFuncPanic) Done() <-chan struct{}      { return c.ch }
func (errsAfterFuncPanic) Err() error                   { return nil }
func (errsAfterFuncPanic) Value(any) any                { return nil }
func (errsAfterFuncPanic) AfterFunc(func()) func() bool { panic("AfterFunc") }

// withVersion is a copy of clientv3's (client/v3/ctx.go, fork 249d76bea7).
func withVersion(ctx context.Context) context.Context {
	md, ok := metadata.FromOutgoingContext(ctx)
	if !ok {
		md = metadata.Pairs(rpctypes.MetadataClientAPIVersionKey, version.APIVersion)
		return metadata.NewOutgoingContext(ctx, md)
	}
	copied := md.Copy()
	copied.Set(rpctypes.MetadataClientAPIVersionKey, version.APIVersion)
	return metadata.NewOutgoingContext(ctx, copied)
}

func echoServer(t *testing.T) *grpc.ClientConn {
	unary := func(_ any, ctx context.Context, dec func(any) error, _ grpc.UnaryServerInterceptor) (any, error) {
		in := new(emptypb.Empty)
		if err := dec(in); err != nil {
			return nil, err
		}
		return new(emptypb.Empty), nil
	}
	stream := func(any, grpc.ServerStream) error { return nil }
	cc := startServer(t, false, nil, unary, stream)
	if err := cc.Invoke(context.Background(), "/t.S/U", new(emptypb.Empty), new(emptypb.Empty)); err != nil {
		t.Fatal(err)
	}
	return cc
}

func TestClientCallCtxPanics(t *testing.T) {
	cc := echoServer(t)
	for name, ctx := range map[string]context.Context{
		"quietValuePanic (item 3)": quietValuePanic{},
		"quietDeadlinePanic (N1)":  quietDeadlinePanic{},
		"errsCancelKeyPanic (N2)":  errsCancelKeyPanic{ch: make(chan struct{})},
		"errsNilCancelCtx (N2)":    errsNilCancelCtx{ch: make(chan struct{})},
		"errsAfterFuncPanic (N3)":  errsAfterFuncPanic{ch: make(chan struct{})},
	} {
		if !panics(func() { _ = cc.Invoke(ctx, "/t.S/U", new(emptypb.Empty), new(emptypb.Empty)) }) {
			t.Errorf("%s: Invoke does not panic", name)
		}
		if !panics(func() { _, _ = cc.NewStream(ctx, &streamDesc, "/t.S/S") }) {
			t.Errorf("%s: NewStream does not panic", name)
		}
	}
	if !panics(func() { withVersion(quietValuePanic{}) }) {
		t.Error("withVersion does not panic on a context whose Value panics")
	}
}

// channelContext is a copy of k8s's (k8s.io/apimachinery/pkg/util/wait, wait.go:120-146).
type channelContext struct{ stopCh <-chan struct{} }

func (c channelContext) Done() <-chan struct{} { return c.stopCh }
func (c channelContext) Err() error {
	select {
	case <-c.stopCh:
		return context.Canceled
	default:
		return nil
	}
}
func (c channelContext) Deadline() (time.Time, bool) { return time.Time{}, false }
func (c channelContext) Value(key any) any           { return nil }

type afterFuncer interface {
	AfterFunc(func()) func() bool
}

// checkClientCtx: what ctxOk (after C3) says of a client call's context.
func checkClientCtx(t *testing.T, name string, ctx context.Context) {
	t.Helper()
	if panics(func() { ctx.Deadline() }) {
		t.Errorf("%s: Deadline panics", name)
	}
	if panics(func() { ctx.Value(new(int)) }) {
		t.Errorf("%s: Value at a *int key panics", name)
	}
	if _, ok := ctx.(afterFuncer); ok {
		t.Errorf("%s: has an AfterFunc method", name)
	}
	md1, ok1 := metadata.FromOutgoingContext(ctx)
	md2, ok2 := metadata.FromOutgoingContext(ctx)
	if ok1 != ok2 || len(md1) != len(md2) {
		t.Errorf("%s: two outgoing metadata %v %v", name, md1, md2)
	}
	for k, v := range md1 {
		if k != strings.ToLower(k) || len(v) == 0 {
			t.Errorf("%s: outgoing key %q %v", name, k, v)
		}
	}
	if _, ok := metadata.FromIncomingContext(ctx); ok {
		t.Errorf("%s: incoming metadata", name)
	}
}

func TestClientContexts(t *testing.T) {
	// A client against an address nobody serves: New does not dial (no DialTimeout), and the
	// contexts are what the client builds whatever the server.
	cli, err := clientv3.New(clientv3.Config{Endpoints: []string{"127.0.0.1:1"}})
	if err != nil {
		t.Fatal(err)
	}
	defer cli.Close()
	sess, cancelSess := context.WithCancel(cli.Ctx()) // NewSession's WithCancel(ops.ctx)
	defer cancelSess()
	obs, cancelObs := context.WithCancel(sess) // Election.Observe's
	defer cancelObs()
	rl := clientv3.WithRequireLeader(context.TODO())
	rlc, cancelRl := context.WithCancel(clientv3.WithRequireLeader(context.Background())) // the lessor's
	defer cancelRl()
	to, cancelTo := context.WithTimeout(context.Background(), time.Minute)
	defer cancelTo()
	open := make(chan struct{})
	closed := make(chan struct{})
	close(closed)
	for name, ctx := range map[string]context.Context{
		"Background": context.Background(), "TODO": context.TODO(), "client.Ctx()": cli.Ctx(),
		"WithCancel(client.Ctx())": sess, "WithCancel(WithCancel(client.Ctx()))": obs,
		"WithRequireLeader(TODO)": rl, "WithCancel(WithRequireLeader(Background))": rlc,
		"WithTimeout(Background)":         to,
		"Append(WithTimeout(Background))": metadata.AppendToOutgoingContext(to, "token", "x"),
		"channelContext open":             channelContext{open}, "channelContext closed": channelContext{closed},
	} {
		checkClientCtx(t, name, ctx)
		checkClientCtx(t, "withVersion("+name+")", withVersion(ctx))
	}
	// grpc calls on them (withVersion of each, as the client makes them) do not panic.
	cc := echoServer(t)
	short, cancelShort := context.WithTimeout(cli.Ctx(), time.Second)
	defer cancelShort()
	for name, ctx := range map[string]context.Context{
		"WithTimeout(client.Ctx())": short, "channelContext open": channelContext{open},
		"WithCancel(WithRequireLeader(Background))": rlc,
	} {
		if panics(func() { _ = cc.Invoke(withVersion(ctx), "/t.S/U", new(emptypb.Empty), new(emptypb.Empty)) }) {
			t.Errorf("%s: Invoke panics", name)
		}
	}
}
