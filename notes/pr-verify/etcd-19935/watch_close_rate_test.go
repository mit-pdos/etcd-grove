// Review: how often a real (fake-gRPC) stream close reports context.Canceled.
package clientv3

import (
	"context"
	"testing"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

func TestReviewCanceledRate(t *testing.T) {
	nonNil := 0
	for i := 0; i < 2000; i++ {
		fc := &closeTestWatchClient{streams: make(chan *closeTestStream, 1)}
		w := NewWatchFromWatchClient(fc, nil)

		chc := make(chan WatchChan, 1)
		go func() { chc <- w.Watch(context.Background(), "a", WithCreatedNotify()) }()
		s := <-fc.streams
		if r := <-s.sent; r.GetCreateRequest() == nil {
			t.Fatalf("expected a create request, got %v", r)
		}
		s.recv <- &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 1}, WatchId: 1, Created: true}
		wch := <-chc
		if resp := <-wch; !resp.Created {
			t.Fatalf("expected the created notification, got %v", resp)
		}
		if err := w.Close(); err != nil {
			nonNil++
		}
	}
	t.Logf("Close() non-nil in %d of 2000 iterations", nonNil)
}
