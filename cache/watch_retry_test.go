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

package cache

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// TestCacheReadyAfterWatchRetry checks that the cache becomes ready again, and
// serves Cache.Watch, after its upstream watch fails and is reopened from a
// fresh Get, whether or not reopening it purges the demux (it does when the
// retried watch does not start right after the last revision the demux saw,
// including when the demux saw none).
func TestCacheReadyAfterWatchRetry(t *testing.T) {
	tests := []struct {
		name string
		// eventAtFirstRev delivers an event at revision 10 on the first stream
		// before it fails.
		eventAtFirstRev bool
		// retryRev is the revision of the Get that precedes the retried watch,
		// which starts at retryRev+1.
		retryRev int64
	}{
		{
			name:            "retry continues from the last observed revision",
			eventAtFirstRev: true,
			retryRev:        10,
		},
		{
			name:            "retry starts past the last observed revision",
			eventAtFirstRev: true,
			retryRev:        12,
		},
		{
			name:            "retry after a stream that observed no events",
			eventAtFirstRev: false,
			retryRev:        12,
		},
	}
	for _, tc := range tests {
		t.Run(tc.name, func(t *testing.T) {
			sw := newStreamWatcher()
			fakeClient := &clientv3.Client{
				Watcher: sw,
				KV: newKVStub(
					&clientv3.GetResponse{Header: &pb.ResponseHeader{Revision: 9}},
					&clientv3.GetResponse{Header: &pb.ResponseHeader{Revision: tc.retryRev}},
				),
			}
			// The upstream watch is retried after a timer of the cache's clock
			// (InitialBackoff), so the clock must run.
			c, err := newCache(fakeClient, "", defaultConfig(), realClock{})
			require.NoError(t, err)
			t.Cleanup(c.Close)

			t.Log("Phase 1: initial watch from revision 10")
			s := sw.nextStream(t)
			require.Equal(t, int64(10), s.rev)
			s.send(t, clientv3.WatchResponse{Created: true, Header: &pb.ResponseHeader{Revision: 9}})
			waitReady(t, c)
			if tc.eventAtFirstRev {
				s.send(t, clientv3.WatchResponse{
					Header: &pb.ResponseHeader{Revision: 10},
					Events: []*clientv3.Event{event(mvccpb.PUT, "/a", 10)},
				})
				waitUntil(t, time.Second, time.Millisecond, func() bool { return c.store.LatestRev() == 10 })
			}

			t.Log("Phase 2: the upstream watch fails")
			s.send(t, clientv3.WatchResponse{
				Canceled:     true,
				CancelReason: "injected failure",
				Header:       &pb.ResponseHeader{Revision: 10},
			})
			waitUntil(t, time.Second, time.Millisecond, func() bool { return !c.Ready() })

			wantRev := tc.retryRev + 1
			t.Logf("Phase 3: the watch is retried from revision %d", wantRev)
			s = sw.nextStream(t)
			require.Equal(t, wantRev, s.rev)
			s.send(t, clientv3.WatchResponse{Created: true, Header: &pb.ResponseHeader{Revision: tc.retryRev}})
			// Should the cache abandon the retried watch and open another,
			// carry on with the newest one; the count is checked at the end.
			s = sw.lastStream(t, s, tc.retryRev)
			s.send(t, clientv3.WatchResponse{
				Header: &pb.ResponseHeader{Revision: wantRev},
				Events: []*clientv3.Event{event(mvccpb.PUT, "/b", wantRev)},
			})
			waitUntil(t, time.Second, time.Millisecond, func() bool { return c.store.LatestRev() == wantRev })
			waitReady(t, c)

			t.Log("Phase 4: Cache.Watch serves the event")
			ctx, cancel := context.WithTimeout(t.Context(), time.Second)
			defer cancel()
			watchCh := c.Watch(ctx, "", clientv3.WithPrefix(), clientv3.WithRev(wantRev))
			select {
			case resp, ok := <-watchCh:
				require.True(t, ok, "Cache.Watch channel closed")
				require.Len(t, resp.Events, 1)
				require.Equal(t, wantRev, resp.Events[0].Kv.ModRevision)
			case <-ctx.Done():
				t.Fatal("Cache.Watch received nothing")
			}
			require.Equal(t, 2, sw.opened, "the retried upstream watch was reopened")
		})
	}
}

func waitReady(t *testing.T, c *Cache) {
	t.Helper()
	ctx, cancel := context.WithTimeout(t.Context(), time.Second)
	defer cancel()
	require.NoError(t, c.WaitReady(ctx), "cache not ready")
}

// streamWatcher is a clientv3.Watcher that gives each Watch call its own
// unbuffered response channel and hands it to the test through streams, so the
// test controls which upstream watch each response is sent on.
type streamWatcher struct {
	streams chan *fakeStream
	opened  int // watches the test has taken from streams
}

type fakeStream struct {
	rev int64 // the revision the watch was opened from
	ch  chan clientv3.WatchResponse
}

func newStreamWatcher() *streamWatcher {
	return &streamWatcher{streams: make(chan *fakeStream, 16)}
}

func (w *streamWatcher) Watch(ctx context.Context, _ string, opts ...clientv3.OpOption) clientv3.WatchChan {
	var op clientv3.Op
	for _, opt := range opts {
		opt(&op)
	}
	s := &fakeStream{rev: op.Rev(), ch: make(chan clientv3.WatchResponse)}
	select {
	case w.streams <- s:
	case <-ctx.Done():
		close(s.ch)
	}
	return s.ch
}

func (w *streamWatcher) RequestProgress(context.Context) error { return nil }

func (w *streamWatcher) Close() error { return nil }

// nextStream returns the next upstream watch the cache opens.
func (w *streamWatcher) nextStream(t *testing.T) *fakeStream {
	t.Helper()
	select {
	case s := <-w.streams:
		w.opened++
		return s
	case <-time.After(time.Second):
		t.Fatal("cache did not open an upstream watch")
		return nil
	}
}

// lastStream gives the cache time to reopen the upstream watch s, confirms
// each watch it reopens with a created response at createdRev, and returns
// the last one. It fails if the cache keeps reopening the watch.
func (w *streamWatcher) lastStream(t *testing.T, s *fakeStream, createdRev int64) *fakeStream {
	t.Helper()
	for reopened := 0; ; reopened++ {
		if reopened == 10 {
			t.Fatalf("cache reopened the watch from revision %d %d times", s.rev, reopened)
		}
		select {
		case next := <-w.streams:
			w.opened++
			s = next
			s.send(t, clientv3.WatchResponse{Created: true, Header: &pb.ResponseHeader{Revision: createdRev}})
		case <-time.After(200 * time.Millisecond):
			return s
		}
	}
}

// send delivers resp on the stream, failing if the cache does not read it.
func (s *fakeStream) send(t *testing.T, resp clientv3.WatchResponse) {
	t.Helper()
	select {
	case s.ch <- resp:
	case <-time.After(time.Second):
		t.Fatalf("watch from revision %d: response not read", s.rev)
	}
}
