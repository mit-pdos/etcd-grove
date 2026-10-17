package clientv3

import (
	"context"
	"testing"
	"time"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
)

// TestReviewerCompactedThenProgressKeepsChannelOpen: MaxWatcherBufferSize = 1. Watch A's
// channel holds rev 2, its buffer the compacted (Canceled, CompactRevision) response; a
// broadcast progress notify (RequestProgress, WatchId -1) then arrives, so the substream waits
// in the backpressure select. Its send case drops buf[0] without the Err() check of the main
// send case: the compacted response is delivered, the substream does not return, the progress
// notify follows it, and the channel is not closed. With 0, the channel closes after the
// compacted response.
func TestReviewerCompactedThenProgressKeepsChannelOpen(t *testing.T) {
	for _, limit := range []int{0, 1} {
		w, fc := blWatcher(limit)
		wa, s := blOpen(t, w, fc, nil, "a", 0)
		s.recv <- blEvent(0, "a", 2)
		s.recv <- blRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 9}, WatchId: 0,
			Canceled: true, CompactRevision: 5}}
		time.Sleep(200 * time.Millisecond)
		// broadcast progress notify, as the server answers RequestProgress
		s.recv <- blRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 10}, WatchId: -1}}
		time.Sleep(200 * time.Millisecond)
		var got []string
		closed := false
	loop:
		for {
			select {
			case r, ok := <-wa:
				if !ok {
					closed = true
					break loop
				}
				switch {
				case r.Err() != nil:
					got = append(got, "err:"+r.Err().Error())
				case r.IsProgressNotify():
					got = append(got, "progress")
				default:
					got = append(got, "events")
				}
			case <-time.After(1 * time.Second):
				break loop
			}
		}
		t.Logf("MaxWatcherBufferSize=%d: received %v, channel closed: %v", limit, got, closed)
		if !closed || len(got) != 2 {
			t.Errorf("MaxWatcherBufferSize=%d: after the compacted response the channel should close; got %v closed=%v", limit, got, closed)
		}
		w.Close()
	}
}

// TestReviewerWatchFromConsumerDeadlocks: MaxWatcherBufferSize = 1. A single goroutine consumes
// watch A and, on its first response, opens watch B on the same context (same gRPC stream).
// A's buffer is full and run() is blocked handing A its next response, so Watch(B) blocks in
// reqc: the consumer never returns to read A, and run() never takes B's request. A deadlock
// (until the context's deadline), not only a stall. With 0, B's create request is sent.
func TestReviewerWatchFromConsumerDeadlocks(t *testing.T) {
	for _, limit := range []int{0, 1} {
		w, fc := blWatcher(limit)
		wa, s := blOpen(t, w, fc, nil, "a", 0)
		for rev := int64(2); rev <= 8; rev++ {
			s.recv <- blEvent(0, "a", rev)
		}
		time.Sleep(200 * time.Millisecond)
		done := make(chan struct{})
		ctx, cancel := context.WithTimeout(context.Background(), 3*time.Second)
		go func() {
			<-wa
			time.Sleep(300 * time.Millisecond) // let run() block on A again
			w.Watch(ctx, "b")
			close(done)
		}()
		sent := false
		select {
		case r := <-s.sent:
			sent = r.GetCreateRequest() != nil
		case <-time.After(2 * time.Second):
		}
		t.Logf("MaxWatcherBufferSize=%d: create request for B sent: %v", limit, sent)
		if !sent {
			t.Errorf("MaxWatcherBufferSize=%d: Watch(B) called from A's consumer blocks", limit)
		}
		cancel()
		<-done
		w.Close()
	}
}
