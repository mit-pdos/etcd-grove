package clientv3

import (
	"context"
	"errors"
	"testing"
	"time"

	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/metadata"
	"google.golang.org/grpc/status"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
)

// ctxRemote behaves like grpc with a canceled context: every unary call fails with Canceled.
type ctxRemote struct{ recordingKVClient }

func (c *ctxRemote) Range(ctx context.Context, _ *pb.RangeRequest, _ ...grpc.CallOption) (*pb.RangeResponse, error) {
	return nil, status.Error(codes.Canceled, ctx.Err().Error())
}

// errStream is a RangeStream client whose first Recv fails with the server's empty-key error
// (what the pre-PR GetStream("") saw: RangeStream returns a stream, Recv fails).
type errStream struct{ grpc.ClientStream }

func (errStream) Recv() (*pb.RangeStreamResponse, error) { return nil, rpctypes.ErrGRPCEmptyKey }
func (errStream) Header() (metadata.MD, error)           { return nil, nil }

type streamRemote struct{ recordingKVClient }

func (c *streamRemote) RangeStream(context.Context, *pb.RangeRequest, ...grpc.CallOption) (grpc.ServerStreamingClient[pb.RangeStreamResponse], error) {
	return errStream{}, nil
}

func TestReviewErrEmptyKeyFacts(t *testing.T) {
	e := rpctypes.ErrEmptyKey
	if e == nil {
		t.Fatal("nil")
	}
	if _, ok := e.(rpctypes.EtcdError); !ok {
		t.Fatalf("type %T", e)
	}
	if errors.Unwrap(e) != nil {
		t.Fatal("not a leaf")
	}
	if _, ok := e.(interface{ GRPCStatus() *status.Status }); ok {
		t.Fatal("has GRPCStatus")
	}
	if _, ok := e.(interface{ Is(error) bool }); ok {
		t.Fatal("has Is")
	}
	_, ok := status.FromError(e)
	t.Logf("Error()=%q status.FromError ok=%v status.Code=%v rpctypes.Error(e)==e: %v",
		e.Error(), ok, status.Code(e), rpctypes.Error(e) == e)
}

// An empty key on an already-canceled context: the PR now reports ErrEmptyKey; the old code
// would have sent the RPC and (as grpc does for a canceled ctx) reported context.Canceled.
func TestReviewCanceledCtx(t *testing.T) {
	ctx, cancel := context.WithCancel(context.Background())
	cancel()
	kv := &kv{remote: &ctxRemote{}}
	_, err := kv.Get(ctx, "")
	t.Logf("Get(canceled ctx, \"\") = %v (Is Canceled: %v)", err, errors.Is(err, context.Canceled))
	_, err = kv.Get(ctx, "a")
	t.Logf("Get(canceled ctx, \"a\") = %v (Is Canceled: %v)", err, errors.Is(err, context.Canceled))
}

// The shape change of GetStream: a nil channel now, a channel carrying the error before.
func TestReviewGetStreamShape(t *testing.T) {
	kv := &kv{remote: &streamRemote{}}
	ch, err := kv.GetStream(context.Background(), "")
	t.Logf("GetStream(\"\") = (ch==nil: %v, %v)", ch == nil, err)
	// The pre-PR shape, by a key the server rejects the same way (the mock rejects every key).
	ch2, err2 := kv.GetStream(context.Background(), "a")
	t.Logf("pre-PR shape: (ch==nil: %v, %v)", ch2 == nil, err2)
	_, e := GetStreamToGetResponse(ch2)
	t.Logf("  error on the channel: %v (== ErrEmptyKey: %v)", e, e == rpctypes.ErrEmptyKey)
	// A caller that ignores GetStream's error and drains the channel now blocks forever.
	done := make(chan struct{})
	go func() { GetStreamToGetResponse(ch); close(done) }()
	select {
	case <-done:
		t.Log("drain of the returned channel returned")
	case <-time.After(200 * time.Millisecond):
		t.Log("drain of the returned (nil) channel blocks forever")
	}
}

// What a grpc server (e.g. the grpc-proxy's kvProxy, which returns kv.Do's error as is) sends
// for an EtcdError: status.Convert, i.e. codes.Unknown, losing the code (pre-existing).
func TestReviewProxyCodeLoss(t *testing.T) {
	for _, g := range []error{rpctypes.ErrGRPCEmptyKey, rpctypes.ErrGRPCNoLeader} {
		e := ContextError(context.Background(), g)
		t.Logf("%v: server code %v, ContextError code %v (wire code via status.Convert: %v)",
			g, status.Code(g), e.(rpctypes.EtcdError).Code(), status.Convert(e).Code())
	}
}
