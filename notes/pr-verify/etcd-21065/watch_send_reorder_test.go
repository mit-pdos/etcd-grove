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
)

// Review copy of watch_send_queue_test.go's fake, recording the order of requests.
// An etcd-like fake watch stream (per-stream ids from 0, a Created response for every create,
// a Canceled response only for a cancel of a live id, a progress response with id -1 for a
// progress request) whose Send can be held: while `held`, Send blocks, as it does when the
// server stops reading the stream (flow control, a busy or stuck server recvLoop).
type roStream struct {
	grpc.ClientStream
	ctx      context.Context
	recv     chan *pb.WatchResponse
	mu       sync.Mutex
	gate     chan struct{} // closed when sends may proceed
	nextID   int64
	live     map[int64]string
	cancels  int
	progress int
	order    []string
}

func (s *roStream) hold() {
	s.mu.Lock()
	s.gate = make(chan struct{})
	s.mu.Unlock()
}

func (s *roStream) release() {
	s.mu.Lock()
	close(s.gate)
	s.mu.Unlock()
}

func (s *roStream) Send(r *pb.WatchRequest) error {
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
		s.order = append(s.order, "create:"+string(r.GetCreateRequest().Key))
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
		s.order = append(s.order, "progress")
		s.progress++
		s.recv <- &pb.WatchResponse{Header: &pb.ResponseHeader{Revision: 1}, WatchId: -1}
	}
	return nil
}

func (s *roStream) Recv() (*pb.WatchResponse, error) {
	select {
	case r := <-s.recv:
		return r, nil
	case <-s.ctx.Done():
		return nil, s.ctx.Err()
	}
}

func (s *roStream) liveIDs() []int64 {
	s.mu.Lock()
	defer s.mu.Unlock()
	var ids []int64
	for id := range s.live {
		ids = append(ids, id)
	}
	return ids
}

func (s *roStream) counts() (int, int, int) {
	s.mu.Lock()
	defer s.mu.Unlock()
	return len(s.live), s.cancels, s.progress
}

type roClient struct{ streams chan *roStream }

func (c *roClient) Watch(ctx context.Context, _ ...grpc.CallOption) (pb.Watch_WatchClient, error) {
	g := make(chan struct{})
	close(g)
	s := &roStream{ctx: ctx, recv: make(chan *pb.WatchResponse, 100000), gate: g, live: map[int64]string{}}
	c.streams <- s
	return s, nil
}

// setup: a keeper watch (id 0) and n watches (ids 1..n), all created.
func roSetup(t *testing.T, n int) (Watcher, *roStream, WatchChan, []context.CancelFunc) {
	fc := &roClient{streams: make(chan *roStream, 4)}
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


// A progress request issued after a Watch (Watch returned, then RequestProgress) can overtake the
// Watch's create on the wire: sendLoop's select picks among the two ready queues at random. The
// new watch then misses the progress notification (it is broadcast to registered substreams only).
func TestWatchProgressOvertakesCreate(t *testing.T) {
	trials, overtook, missed := 40, 0, 0
	for i := 0; i < trials; i++ {
		func() {
			w, s, _, cancels := roSetup(t, 1)
			defer w.Close()
			s.hold()
			cancels[0]() // the cancel's Send blocks
			time.Sleep(50 * time.Millisecond)
			wchc := make(chan WatchChan, 1)
			go func() {
				wchc <- w.Watch(context.Background(), "new", WithCreatedNotify())
				w.RequestProgress(context.Background())
			}()
			time.Sleep(50 * time.Millisecond)
			s.release()
			wch := <-wchc
			got := false
			to := time.After(500 * time.Millisecond)
		loop:
			for {
				select {
				case r := <-wch:
					if r.IsProgressNotify() {
						got = true
						break loop
					}
				case <-to:
					break loop
				}
			}
			s.mu.Lock()
			o := append([]string(nil), s.order...)
			s.mu.Unlock()
			for _, x := range o {
				if x == "progress" {
					overtook++
					break
				}
				if x == "create:new" {
					break
				}
			}
			if i == 0 {
				t.Logf("order of requests: %v", o)
			}
			if !got {
				missed++
			}
		}()
	}
	t.Logf("%d trials: progress before the new create in %d; the new watch missed the progress notification in %d", trials, overtook, missed)
	if missed > 0 {
		t.Errorf("a watch made before RequestProgress missed its progress notification in %d/%d trials", missed, trials)
	}
}
