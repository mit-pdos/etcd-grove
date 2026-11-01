package clientv3

import (
	"context"
	"errors"
	"testing"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

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

var stages [8]int

func oneTrial() (int, error) {
	fc := &fakeWatchClient{streams: make(chan *fakeWatchStream, 4)}
	c := &Client{}
	c.lg.Store(zap.NewNop())
	w := NewWatchFromWatchClient(fc, c)
	ctx, cancel := context.WithCancel(context.Background())
	chc := make(chan WatchChan, 1)
	go func() { chc <- w.Watch(ctx, "a") }()
	s1 := <-fc.streams
	if _, err := waitSent(s1); err != nil { // the create request
		return 0, err
	}
	s1.recv <- fakeRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 1}, WatchId: 1, Created: true}}
	s1.gate <- struct{}{}
	<-chc
	// Make run() busy in a Send (a progress request), then cancel the watch's context (its
	// substream goroutine exits, closing, and waits on closingc) and queue an event for it.
	go w.RequestProgress(context.Background())
	if _, err := waitSent(s1); err != nil {
		return 1, err
	}
	cancel()
	ev := &mvccpb.Event{Kv: &mvccpb.KeyValue{Key: []byte("a"), ModRevision: 2}}
	s1.recv <- fakeRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: 1, Events: []*mvccpb.Event{ev}}}
	time.Sleep(settle)
	s1.gate <- struct{}{}
	// If run() takes the event first, it cannot dispatch it and sends a cancel request.
	r, err := waitSent(s1)
	if err != nil || r.GetCancelRequest() == nil {
		return 2, errTrialLost
	}
	// The server answers the cancel (as etcd's does), then the stream fails transiently. A
	// progress request waits on reqc, so that run() can be made busy again (in its Send) after
	// it takes the canceled response, while the error reaches errc.
	s1.recv <- fakeRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: 1, Canceled: true}}
	s1.recv <- fakeRecv{err: status.Error(codes.Unavailable, "transient")}
	go w.RequestProgress(context.Background())
	time.Sleep(settle)
	s1.gate <- struct{}{}
	if r, err := waitSent(s1); err != nil || r.GetProgressRequest() == nil {
		return 3, errTrialLost
	}
	time.Sleep(settle)
	s1.gate <- struct{}{}
	// If run() took the canceled response (closing the substream's recvc) and takes the error
	// before the closing substream, it reconnects and resumes the closing substream.
	var s2 *fakeWatchStream
	select {
	case s2 = <-fc.streams:
	case <-time.After(100 * time.Millisecond):
		return 4, errTrialLost
	}
	if _, err := waitSent(s2); err != nil { // the resumed create request
		return 5, err
	}
	s2.recv <- fakeRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: 2, Created: true}}
	time.Sleep(settle)
	s2.gate <- struct{}{}
	// If run() takes the created response first, unicastResponse selects between a send on
	// the substream's closed recvc (a panic) and its closed donec.
	time.Sleep(settle)
	return 6, errTrialLost
}

// TestWatchResumeClosingSubstream crashes the test binary with "panic: send on closed
// channel" (watch.go, unicastResponse) once the scheduler picks the interleaving above.
func TestWatchResumeClosingSubstream(t *testing.T) {
	for i := 0; i < 3000; i++ {
		st, err := oneTrial()
		stages[st]++
		if !errors.Is(err, errTrialLost) {
			t.Fatal(err)
		}
	}
	t.Logf("no panic; trials lost at each stage: %v", stages)
}
