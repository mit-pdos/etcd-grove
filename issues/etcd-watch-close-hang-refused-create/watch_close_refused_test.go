package clientv3

import (
	"context"
	"testing"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

type refuseStream struct {
	grpc.ClientStream
	ctx  context.Context
	sent chan *pb.WatchRequest
	gate chan struct{}
	recv chan *pb.WatchResponse
}

func (s *refuseStream) Send(r *pb.WatchRequest) error {
	s.sent <- r
	select {
	case <-s.gate:
	case <-s.ctx.Done():
	}
	return nil
}

func (s *refuseStream) Recv() (*pb.WatchResponse, error) {
	select {
	case r := <-s.recv:
		return r, nil
	case <-s.ctx.Done():
		return nil, s.ctx.Err()
	}
}

type refuseClient struct{ streams chan *refuseStream }

func (c *refuseClient) Watch(ctx context.Context, _ ...grpc.CallOption) (pb.Watch_WatchClient, error) {
	s := &refuseStream{ctx: ctx, sent: make(chan *pb.WatchRequest, 16), gate: make(chan struct{}, 16),
		recv: make(chan *pb.WatchResponse, 16)}
	c.streams <- s
	return s, nil
}

// TestWatchCloseAfterRefusedCreate: the server refuses a create (as etcd does when the watch is
// not permitted); run closes the substream's recvc and forgets it (resuming[0] = nil), and the
// substream's goroutine then waits to post on closingc. If run stops (Close) before it takes it,
// its teardown neither counts nor receives it, and waits in wg.Wait() forever: Close hangs.
func TestWatchCloseAfterRefusedCreate(t *testing.T) {
	for i := 0; i < 2000; i++ {
		fc := &refuseClient{streams: make(chan *refuseStream, 1)}
		c := &Client{}
		c.lg.Store(zap.NewNop())
		w := NewWatchFromWatchClient(fc, c)
		chc := make(chan WatchChan, 1)
		go func() { chc <- w.Watch(context.Background(), "a") }()
		s := <-fc.streams
		<-s.sent
		s.gate <- struct{}{}
		// a progress request keeps run busy (its Send blocks) while the refusal arrives
		go w.RequestProgress(context.Background())
		<-s.sent
		s.recv <- &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 1}, WatchId: -1, Created: true,
			Canceled: true, CancelReason: "etcdserver: permission denied"}
		time.Sleep(time.Millisecond)
		// release run: it takes the refusal; close the watcher meanwhile
		done := make(chan struct{})
		s.gate <- struct{}{}
		go func() { w.Close(); close(done) }()
		select {
		case <-done:
		case <-time.After(2 * time.Second):
			t.Fatalf("trial %d: watcher.Close() hangs", i)
		}
		<-chc
	}
}
