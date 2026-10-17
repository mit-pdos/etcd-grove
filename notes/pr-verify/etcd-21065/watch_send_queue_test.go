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
	"fmt"
	"sync"
	"testing"
	"time"

	"go.uber.org/zap"
	"google.golang.org/grpc"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
)

// An etcd-like fake watch stream (per-stream ids from 0, a Created response for every create,
// a Canceled response only for a cancel of a live id, a progress response with id -1 for a
// progress request) whose Send can be held: while `held`, Send blocks, as it does when the
// server stops reading the stream (flow control, a busy or stuck server recvLoop).
type sqStream struct {
	grpc.ClientStream
	ctx      context.Context
	recv     chan *pb.WatchResponse
	mu       sync.Mutex
	gate     chan struct{} // closed when sends may proceed
	nextID   int64
	live     map[int64]string
	cancels  int
	progress int
}

func (s *sqStream) hold() {
	s.mu.Lock()
	s.gate = make(chan struct{})
	s.mu.Unlock()
}

func (s *sqStream) release() {
	s.mu.Lock()
	close(s.gate)
	s.mu.Unlock()
}

func (s *sqStream) Send(r *pb.WatchRequest) error {
	s.mu.Lock()
	g := s.gate
	s.mu.Unlock()
	select {
	case <-g:
	case <-s.ctx.Done():
		return s.ctx.Err()
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	switch {
	case r.GetCreateRequest() != nil:
		id := s.nextID
		s.nextID++
		s.live[id] = string(r.GetCreateRequest().Key)
		s.recv <- &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 1}, WatchId: id, Created: true}
	case r.GetCancelRequest() != nil:
		s.cancels++
		id := r.GetCancelRequest().WatchId
		if _, ok := s.live[id]; ok {
			delete(s.live, id)
			s.recv <- &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 1}, WatchId: id, Canceled: true}
		}
	case r.GetProgressRequest() != nil:
		s.progress++
		s.recv <- &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 1}, WatchId: -1}
	}
	return nil
}

func (s *sqStream) Recv() (*pb.WatchResponse, error) {
	select {
	case r := <-s.recv:
		return r, nil
	case <-s.ctx.Done():
		return nil, s.ctx.Err()
	}
}

func (s *sqStream) liveWatches() map[int64]string {
	s.mu.Lock()
	defer s.mu.Unlock()
	m := make(map[int64]string, len(s.live))
	for id, key := range s.live {
		m[id] = key
	}
	return m
}

// liveIDs: the ids of the watches the server holds (used by watch_send_reorder_test.go).
func (s *sqStream) liveIDs() []int64 {
	var ids []int64
	for id := range s.liveWatches() {
		ids = append(ids, id)
	}
	return ids
}

func (s *sqStream) counts() (int, int, int) {
	s.mu.Lock()
	defer s.mu.Unlock()
	return len(s.live), s.cancels, s.progress
}

type sqClient struct{ streams chan *sqStream }

func (c *sqClient) Watch(ctx context.Context, _ ...grpc.CallOption) (pb.Watch_WatchClient, error) {
	g := make(chan struct{})
	close(g)
	s := &sqStream{ctx: ctx, recv: make(chan *pb.WatchResponse, 100000), gate: g, live: map[int64]string{}}
	c.streams <- s
	return s, nil
}

// setup: a keeper watch (id 0) and n watches (ids 1..n), all created.
func sqSetup(t *testing.T, n int) (Watcher, *sqStream, WatchChan, []context.CancelFunc) {
	fc := &sqClient{streams: make(chan *sqStream, 4)}
	c := &Client{}
	c.lg.Store(zap.NewNop())
	w := NewWatchFromWatchClient(fc, c)
	keeper := w.Watch(context.Background(), "keeper", WithCreatedNotify())
	<-keeper
	s := <-fc.streams
	var cancels []context.CancelFunc
	for i := 0; i < n; i++ {
		ctx, cancel := context.WithCancel(context.Background())
		wc := w.Watch(ctx, fmt.Sprintf("k%d", i), WithCreatedNotify())
		<-wc
		cancels = append(cancels, cancel)
	}
	return w, s, keeper, cancels
}

// The user closes n watches at once while the stream's Send is held (the server is not reading
// for a while); then the stream recovers. Every closed watch must end up cancelled on the
// server, if need be after the server sends it another event. With the bounded best-effort
// queue, the cancels beyond its capacity are dropped, and the client never sends them again:
// `cancelSet` already holds their ids, so their later events are ignored without a new cancel.
func TestWatchCancelStormLeaksServerWatchers(t *testing.T) {
	const n = 300
	w, s, _, cancels := sqSetup(t, n)
	defer w.Close()

	s.hold()
	for _, cancel := range cancels {
		cancel()
	}
	time.Sleep(500 * time.Millisecond) // run() takes the closed substreams from closingc
	s.release()
	time.Sleep(500 * time.Millisecond)
	live1, sent1, _ := s.counts()

	// the server sends one event to every watch it still has but the keeper
	for id, key := range s.liveWatches() {
		if id == 0 {
			continue
		}
		ev := &mvccpb.Event{Kv: &mvccpb.KeyValue{Key: []byte(key), ModRevision: 2}}
		s.recv <- &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 2}, WatchId: id, Events: []*mvccpb.Event{ev}}
	}
	time.Sleep(500 * time.Millisecond)
	live2, sent2, _ := s.counts()
	t.Logf("closed %d watches: server got %d cancel requests, %d watches left on the server (keeper included); after one more event each: %d cancel requests, %d watches left",
		n, sent1, live1, sent2, live2)
	if live2 != 1 {
		t.Errorf("%d closed watches are still registered on the server, and the client will never cancel them", live2-1)
	}
}

// While the best-effort queue is full of cancels, RequestProgress returns nil but its request is
// dropped: the server never sees it and no progress notification comes.
func TestWatchRequestProgressDroppedWhenQueueFull(t *testing.T) {
	const n = 200
	w, s, keeper, cancels := sqSetup(t, n)
	defer w.Close()

	s.hold()
	for _, cancel := range cancels {
		cancel()
	}
	time.Sleep(500 * time.Millisecond)
	errc := make(chan error, 1)
	go func() { errc <- w.RequestProgress(context.Background()) }()
	time.Sleep(200 * time.Millisecond)
	s.release()

	var rpErr error = fmt.Errorf("RequestProgress has not returned")
	select {
	case rpErr = <-errc:
	case <-time.After(2 * time.Second):
	}
	got := false
	timeout := time.After(2 * time.Second)
loop:
	for {
		select {
		case r := <-keeper:
			if r.IsProgressNotify() {
				got = true
				break loop
			}
		case <-timeout:
			break loop
		}
	}
	_, _, prog := s.counts()
	t.Logf("RequestProgress returned %v; progress requests the server got: %d; keeper got a progress notification: %v", rpErr, prog, got)
	if rpErr == nil && !got {
		t.Errorf("RequestProgress returned nil, but its request was dropped: no progress notification")
	}
}
