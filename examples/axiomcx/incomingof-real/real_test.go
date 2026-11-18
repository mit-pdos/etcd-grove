package incomingofreal

import (
	"context"
	"errors"
	"fmt"
	"reflect"
	"testing"

	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
	clientv3 "go.etcd.io/etcd/client/v3"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"
)

var handlerDescs = []string{"etcdserver: mvcc: required revision is a future revision",
	"etcdserver: mvcc: required revision has been compacted"}

func methods(v any) []string {
	t := reflect.TypeOf(v)
	var out []string
	for i := 0; i < t.NumMethod(); i++ {
		out = append(out, t.Method(i).Name+" "+t.Method(i).Type.String())
	}
	return out
}

type isIface interface{ Is(error) bool }

func TestRealTypes(t *testing.T) {
	t.Logf("ErrFutureRev: %T %q methods=%v comparable=%v", rpctypes.ErrFutureRev, rpctypes.ErrFutureRev.Error(),
		methods(rpctypes.ErrFutureRev), reflect.TypeOf(rpctypes.ErrFutureRev).Comparable())
	for _, e := range []error{context.Canceled, context.DeadlineExceeded} {
		_, hasIs := e.(isIface)
		_, isEtcd := e.(rpctypes.EtcdError)
		t.Logf("%T %q methods=%v hasIs=%v EtcdError=%v", e, e.Error(), methods(e), hasIs, isEtcd)
		if hasIs || isEtcd {
			t.Fatal("ctxErrShape false")
		}
		for _, h := range handlerDescs {
			if e.Error() == h {
				t.Fatal("message is a handler desc")
			}
		}
		if errors.Is(e, rpctypes.ErrFutureRev) {
			t.Fatal("Is true")
		}
	}
	// T3 candidates: true results whose dynamic type is not EtcdError
	cands := map[string]error{
		"equal EtcdError (via rpctypes.Error of status)": rpctypes.Error(status.Error(codes.OutOfRange, "etcdserver: mvcc: required revision is a future revision")),
		"wrapped %w (not a leaf)":                         fmt.Errorf("x: %w", rpctypes.ErrFutureRev),
		"errors.Join (Unwrap []error, not a leaf)":        errors.Join(rpctypes.ErrFutureRev),
		"*status.Error same desc":                         status.Error(codes.OutOfRange, "etcdserver: mvcc: required revision is a future revision"),
		"pointer to EtcdError":                            &rpctypes.EtcdError{},
		"ErrGRPCFutureRev":                                rpctypes.ErrGRPCFutureRev,
	}
	for n, e := range cands {
		_, hasIs := e.(isIface)
		_, isEtcd := e.(rpctypes.EtcdError)
		t.Logf("%-48s %T Is=%v hasIs=%v EtcdError=%v", n, e, errors.Is(e, rpctypes.ErrFutureRev), hasIs, isEtcd)
	}
}

// ContextError on the invoker's error for a done context returns ctx.Err() itself.
func TestContextErrorRaw(t *testing.T) {
	ctx, cancel := context.WithCancel(context.Background())
	cancel()
	in := status.FromContextError(ctx.Err()).Err()
	out := clientv3.ContextError(ctx, in)
	t.Logf("in %T %q -> out %T %q same=%v", in, in.Error(), out, out.Error(), out == context.Canceled)
	if out != context.Canceled {
		t.Fatal("not raw")
	}
	// twice (kv.Get: ContextError over kv.Do's ContextError)
	out2 := clientv3.ContextError(ctx, out)
	if out2 != context.Canceled {
		t.Fatal("not raw twice")
	}
	dctx, dcancel := context.WithTimeout(context.Background(), 0)
	defer dcancel()
	<-dctx.Done()
	in = status.FromContextError(dctx.Err()).Err()
	out = clientv3.ContextError(dctx, in)
	t.Logf("deadline: in %q -> out %T same=%v", in.Error(), out, out == context.DeadlineExceeded)
	// cause contexts: Err is still Canceled
	cctx, ccancel := context.WithCancelCause(context.Background())
	ccancel(rpctypes.ErrFutureRev)
	out = clientv3.ContextError(cctx, status.FromContextError(cctx.Err()).Err())
	t.Logf("cause ctx: out %T %q", out, out.Error())
	if out != context.Canceled {
		t.Fatal("cause leaked")
	}
	// status Canceled while ctx not done: the status error is returned (first disjunct)
	out = clientv3.ContextError(context.Background(), status.Error(codes.Canceled, "context canceled"))
	t.Logf("ctx live, status Canceled: out %T %q", out, out.Error())
	// server's ErrGRPCCanceled maps to EtcdError
	out = clientv3.ContextError(ctx, rpctypes.ErrGRPCCanceled)
	t.Logf("server ErrGRPCCanceled with done ctx: out %T %q", out, out.Error())
}
