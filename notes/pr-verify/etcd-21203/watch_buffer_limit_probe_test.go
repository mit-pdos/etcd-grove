// Copyright 2026 The etcd Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package clientv3

import (
	"context"
	"testing"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc"
	"google.golang.org/grpc/codes"
	"google.golang.org/grpc/status"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
)

type blRecv struct {
	resp *pb.WatchResponse
	err  error
}

// blStream is a fake gRPC watch stream: the test plays the server.
type blStream struct {
	grpc.ClientStream
	ctx  context.Context
	sent chan *pb.WatchRequest
	recv chan blRecv
}

func (s *blStream) Send(r *pb.WatchRequest) error {
	select {
	case s.sent <- r:
	case <-s.ctx.Done():
	}
	return nil
}

func (s *blStream) Recv() (*pb.WatchResponse, error) {
	select {
	case r := <-s.recv:
		return r.resp, r.err
	case <-s.ctx.Done():
		return nil, s.ctx.Err()
	}
}

type blWatchClient struct{ streams chan *blStream }

func (c *blWatchClient) Watch(ctx context.Context, _ ...grpc.CallOption) (pb.Watch_WatchClient, error) {
	s := &blStream{ctx: ctx, sent: make(chan *pb.WatchRequest, 16), recv: make(chan blRecv, 64)}
	c.streams <- s
	return s, nil
}

func blCreate(t *testing.T, s *blStream) *pb.WatchCreateRequest {
	t.Helper()
	select {
	case r := <-s.sent:
		if r.GetCreateRequest() == nil {
			t.Fatalf("expected a create request, got %v", r)
		}
		return r.GetCreateRequest()
	case <-time.After(5 * time.Second):
		t.Fatal("no create request")
	}
	return nil
}

func blEvent(id int64, key string, rev int64) blRecv {
	ev := &mvccpb.Event{Kv: &mvccpb.KeyValue{Key: []byte(key), ModRevision: rev}}
	return blRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: rev}, WatchId: id, Events: []*mvccpb.Event{ev}}}
}

func blWatcher(limit int) (Watcher, *blWatchClient) {
	fc := &blWatchClient{streams: make(chan *blStream, 4)}
	c := &Client{}
	c.cfg.MaxWatcherBufferSize = limit
	c.lg.Store(zap.NewNop())
	return NewWatchFromWatchClient(fc, c), fc
}

// blOpen opens a watch on key with id on stream s (the first watch opens the stream).
func blOpen(t *testing.T, w Watcher, fc *blWatchClient, s *blStream, key string, id int64) (WatchChan, *blStream) {
	ch := make(chan WatchChan, 1)
	go func() { ch <- w.Watch(context.Background(), key, WithCreatedNotify()) }()
	if s == nil {
		s = <-fc.streams
	}
	blCreate(t, s)
	s.recv <- blRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 1}, WatchId: id, Created: true}}
	wch := <-ch
	<-wch // the created notification
	return wch, s
}

// TestWatchBufferLimitStallsOtherWatchers: two watches on the same context share one gRPC
// stream. Watch A's consumer is slow (it does not read); watch B's reads. With
// MaxWatcherBufferSize = 2, once A's buffer is full A's goroutine stops receiving, so run()
// blocks handing A its next response, and B's event, behind it on the stream, is never
// delivered while A is not read. With no limit (0) B gets its event.
func TestWatchBufferLimitStallsOtherWatchers(t *testing.T) {
	for _, limit := range []int{0, 2} {
		w, fc := blWatcher(limit)
		_, s := blOpen(t, w, fc, nil, "a", 0)
		wb, _ := blOpen(t, w, fc, s, "b", 1)
		// A's events, not consumed: one fills outc's one-slot buffer, two fill A's buffer,
		// the fourth waits in A's goroutine, the fifth in run()
		for rev := int64(2); rev <= 6; rev++ {
			s.recv <- blEvent(0, "a", rev)
		}
		s.recv <- blEvent(1, "b", 7)
		got := false
		select {
		case resp := <-wb:
			got = len(resp.Events) == 1
		case <-time.After(2 * time.Second):
		}
		t.Logf("MaxWatcherBufferSize=%d: watch B received its event: %v", limit, got)
		if !got {
			t.Errorf("MaxWatcherBufferSize=%d: watch B's event is not delivered while watch A is not read", limit)
		}
		w.Close()
	}
}

// TestWatchBufferLimitResumeLosesEvent: with MaxWatcherBufferSize = 1, watch A's channel holds
// the event at revision 2 (its one-slot buffer), A's buffer the event at revision 3, and its
// goroutine waits (backpressure) with the event at revision 4, which already advanced the
// watch's resume revision to 5. A retryable stream error then makes the client resume: the
// goroutine returns, dropping revision 4, and the resume request starts at revision 5. The
// consumer, reading afterwards, sees revisions 2, 3 and then 5: revision 4 is lost. With no
// limit (0), revision 4 is in the buffer and is delivered.
func TestWatchBufferLimitResumeLosesEvent(t *testing.T) {
	for _, limit := range []int{0, 1} {
		w, fc := blWatcher(limit)
		wa, s1 := blOpen(t, w, fc, nil, "a", 0)
		s1.recv <- blEvent(0, "a", 2)
		s1.recv <- blEvent(0, "a", 3)
		s1.recv <- blEvent(0, "a", 4)
		time.Sleep(200 * time.Millisecond) // A's goroutine has taken all three
		s1.recv <- blRecv{err: status.Error(codes.Unavailable, "transient")}
		s2 := <-fc.streams
		cr := blCreate(t, s2) // A's resume
		s2.recv <- blRecv{resp: &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: cr.StartRevision - 1}, WatchId: 0, Created: true}}
		s2.recv <- blEvent(0, "a", cr.StartRevision)
		var revs []int64
		timeout := time.After(2 * time.Second)
	loop:
		for len(revs) < 4 {
			select {
			case resp := <-wa:
				for _, ev := range resp.Events {
					revs = append(revs, ev.Kv.ModRevision)
				}
			case <-timeout:
				break loop
			}
		}
		t.Logf("MaxWatcherBufferSize=%d: resume from revision %d; revisions received: %v", limit, cr.StartRevision, revs)
		for i, rev := range revs {
			if rev != int64(2+i) {
				t.Errorf("MaxWatcherBufferSize=%d: revisions received %v, want 2, 3, 4, 5 (revision %d lost)", limit, revs, 2+i)
				break
			}
		}
		w.Close()
	}
}
