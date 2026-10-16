// Reproduction of issues/etcd-watch-cancel-before-created-leak.md.
//
// Package clientv3, file client/v3/watch_cancel_before_created_test.go of go.etcd.io/etcd
// (module go.etcd.io/etcd/client/v3), at the etcd pin of etc/goose.py: 107edf7e4 (branch
// goose-lean of upamanyus/etcd).
//
// Run, in client/v3:
//
//	GOTOOLCHAIN=go1.27.1 go test . -run '^TestWatchCancelBeforeCreatedLeaksServerWatcher$' -count=1
//
// Fails at the pin (shows the bug): "no cancel request for server watch 1 of a canceled Watch
// (got <nil>): it leaks".
package clientv3

import (
	"context"
	"testing"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

type fakeWatchStream struct {
	grpc.ClientStream
	ctx   context.Context
	sent  chan *pb.WatchRequest
	resps chan *pb.WatchResponse
}

func (f *fakeWatchStream) Send(r *pb.WatchRequest) error { f.sent <- r; return nil }
func (f *fakeWatchStream) Recv() (*pb.WatchResponse, error) {
	select {
	case r := <-f.resps:
		return r, nil
	case <-f.ctx.Done():
		return nil, f.ctx.Err()
	}
}
func (f *fakeWatchStream) Context() context.Context { return f.ctx }
func (f *fakeWatchStream) CloseSend() error         { return nil }

type fakeWatchClient struct{ s *fakeWatchStream }

func (c *fakeWatchClient) Watch(ctx context.Context, _ ...grpc.CallOption) (pb.Watch_WatchClient, error) {
	c.s.ctx = ctx
	return c.s, nil
}

func nextSent(s *fakeWatchStream) *pb.WatchRequest {
	select {
	case r := <-s.sent:
		return r
	case <-time.After(2 * time.Second):
		return nil
	}
}

func TestWatchCancelBeforeCreatedLeaksServerWatcher(t *testing.T) {
	s := &fakeWatchStream{sent: make(chan *pb.WatchRequest, 16), resps: make(chan *pb.WatchResponse)}
	w := &watcher{remote: &fakeWatchClient{s}, streams: make(map[string]*watchGRPCStream), lg: zap.NewNop()}
	defer w.Close()

	go w.Watch(context.Background(), "a") // keeps the stream open; created as id 0
	if r := nextSent(s); r == nil || r.GetCreateRequest() == nil {
		t.Fatalf("expected create for a, got %v", r)
	}
	s.resps <- &pb.WatchResponse{Header: &pb.ResponseHeader{}, WatchId: 0, Created: true}

	ctx2, cancel2 := context.WithCancel(context.Background())
	done := make(chan WatchChan)
	go func() { done <- w.Watch(ctx2, "b") }()
	if r := nextSent(s); r == nil || string(r.GetCreateRequest().GetKey()) != "b" {
		t.Fatalf("expected create for b, got %v", r)
	}
	cancel2() // canceled before the server's Created response
	<-done
	time.Sleep(200 * time.Millisecond)

	s.resps <- &pb.WatchResponse{Header: &pb.ResponseHeader{}, WatchId: 1, Created: true}
	if r := nextSent(s); r == nil || r.GetCancelRequest().GetWatchId() != 1 {
		t.Errorf("no cancel request for server watch 1 of a canceled Watch (got %v): it leaks", r)
	}
}
