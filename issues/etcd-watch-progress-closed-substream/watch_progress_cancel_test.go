package clientv3

import (
	"context"
	"errors"
	"testing"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
)

// A fake gRPC watch stream; the test plays the server. Send blocks until the test opens the
// gate, so that the test can make run() busy while it readies two of its select's cases.
type fakeWatchStream struct {
	grpc.ClientStream
	ctx  context.Context
	sent chan *pb.WatchRequest
	gate chan struct{}
	recv chan fakeRecv
}

type fakeRecv struct {
	resp *pb.WatchResponse
	err  error
}

func (s *fakeWatchStream) Send(r *pb.WatchRequest) error {
	s.sent <- r
	select {
	case <-s.gate:
	case <-s.ctx.Done():
	}
	return nil
}

func (s *fakeWatchStream) Recv() (*pb.WatchResponse, error) {
	select {
	case r := <-s.recv:
		return r.resp, r.err
	case <-s.ctx.Done():
		return nil, s.ctx.Err()
	}
}

type fakeWatchClient struct{ streams chan *fakeWatchStream }

func (c *fakeWatchClient) Watch(ctx context.Context, _ ...grpc.CallOption) (pb.Watch_WatchClient, error) {
	s := &fakeWatchStream{
		ctx: ctx, sent: make(chan *pb.WatchRequest, 16),
		gate: make(chan struct{}, 16), recv: make(chan fakeRecv, 16),
	}
	c.streams <- s
	return s, nil
}

var errTrialLost = errors.New("interleaving not hit")

func waitSent(s *fakeWatchStream) (*pb.WatchRequest, error) {
	select {
	case r := <-s.sent:
		return r, nil
	case <-time.After(100 * time.Millisecond):
		return nil, errTrialLost
	}
}

const settle = 3 * time.Millisecond

// One trial: a watch is canceled with an event in flight, the server answers the cancel
// request run() sends (run() closes the substream's recvc, the substream still registered),
// and a progress request's broadcast response (watch id -1) reaches run() before the closing
// substream does: broadcastResponse selects between a send on the closed recvc and the
// closed donec.
func progressTrial() (int, error) {
	fc := &fakeWatchClient{streams: make(chan *fakeWatchStream, 4)}
	c := &Client{}
	c.lg.Store(zap.NewNop())
	w := NewWatchFromWatchClient(fc, c)
	ctx, cancel := context.WithCancel(context.Background())
	chc := make(chan WatchChan, 1)
	go func() { chc <- w.Watch(ctx, "a") }()
	s1 := <-fc.streams
	if _, err := waitSent(s1); err != nil {
		return 0, err
	}
	s1.recv <- fakeRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 1}, WatchId: 1, Created: true}}
	s1.gate <- struct{}{}
	<-chc
	go w.RequestProgress(context.Background())
	if _, err := waitSent(s1); err != nil {
		return 1, err
	}
	cancel()
	ev := &mvccpb.Event{Kv: &mvccpb.KeyValue{Key: []byte("a"), ModRevision: 2}}
	s1.recv <- fakeRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: 1, Events: []*mvccpb.Event{ev}}}
	time.Sleep(settle)
	s1.gate <- struct{}{}
	r, err := waitSent(s1)
	if err != nil || r.GetCancelRequest() == nil {
		return 2, errTrialLost
	}
	// The server answers the cancel; a progress request waits on reqc.
	s1.recv <- fakeRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: 1, Canceled: true}}
	go w.RequestProgress(context.Background())
	time.Sleep(settle)
	s1.gate <- struct{}{}
	if r, err := waitSent(s1); err != nil || r.GetProgressRequest() == nil {
		return 3, errTrialLost
	}
	// The server answers the progress request as etcd's does when every watcher is synced:
	// a response with watch id -1 and no events, broadcast by the client.
	s1.recv <- fakeRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: -1}}
	time.Sleep(settle)
	s1.gate <- struct{}{}
	time.Sleep(settle)
	return 4, errTrialLost
}

// TestWatchProgressAfterServerCancel crashes the test binary with "panic: send on closed
// channel" (watch.go, broadcastResponse) once the scheduler picks the interleaving above.
func TestWatchProgressAfterServerCancel(t *testing.T) {
	var lost [8]int
	for i := 0; i < 3000; i++ {
		st, err := progressTrial()
		lost[st]++
		if !errors.Is(err, errTrialLost) {
			t.Fatal(err)
		}
	}
	t.Logf("no panic; trials lost at each stage: %v", lost)
}
