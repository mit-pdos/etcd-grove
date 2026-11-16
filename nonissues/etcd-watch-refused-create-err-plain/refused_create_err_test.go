package clientv3

import (
	"context"
	"errors"
	"testing"

	"go.uber.org/zap"
	"google.golang.org/grpc"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/v3rpc/rpctypes"
)

type ceStream struct {
	grpc.ClientStream
	ctx  context.Context
	sent chan *pb.WatchRequest
	recv chan *pb.WatchResponse
}

func (s *ceStream) Send(r *pb.WatchRequest) error { s.sent <- r; return nil }
func (s *ceStream) Recv() (*pb.WatchResponse, error) {
	select {
	case r := <-s.recv:
		return r, nil
	case <-s.ctx.Done():
		return nil, s.ctx.Err()
	}
}

type ceClient struct{ streams chan *ceStream }

func (c *ceClient) Watch(ctx context.Context, _ ...grpc.CallOption) (pb.Watch_WatchClient, error) {
	s := &ceStream{ctx: ctx, sent: make(chan *pb.WatchRequest, 16), recv: make(chan *pb.WatchResponse, 16)}
	c.streams <- s
	return s, nil
}

// The member's answer to a watch the user may not read (server/etcdserver/api/v3rpc/watch.go,
// isWatchPermitted's refusal): the client's close error is an errors.New of the reason.
func TestRefusedCreateErrPlain(t *testing.T) {
	for _, reason := range []string{rpctypes.ErrGRPCPermissionDenied.Error(), "mvcc: watcher range is empty"} {
		fc := &ceClient{streams: make(chan *ceStream, 1)}
		c := &Client{}
		c.lg.Store(zap.NewNop())
		w := NewWatchFromWatchClient(fc, c)
		chc := make(chan WatchChan, 1)
		go func() { chc <- w.Watch(context.Background(), "a") }()
		s := <-fc.streams
		<-s.sent
		s.recv <- &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 1}, WatchId: -1, Created: true,
			Canceled: true, CancelReason: reason}
		wc := <-chc
		wr, ok := <-wc
		if !ok {
			t.Fatalf("channel closed without a response")
		}
		var ee rpctypes.EtcdError
		t.Logf("reason %q: closeErr %T %q; Err() %T %q; EtcdError? %v", reason, wr.closeErr, wr.closeErr,
			wr.Err(), wr.Err(), errors.As(wr.Err(), &ee))
		go w.Close()
	}
}
