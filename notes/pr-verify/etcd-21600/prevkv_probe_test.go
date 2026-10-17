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
	"fmt"
	"testing"
	"time"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/api/v3/mvccpb"
	clientv3 "go.etcd.io/etcd/client/v3"
)

// A WithPrevKV watcher that reads slower than the store's history window
// advances gets update events with PrevKv == nil, although the key existed
// before each update (etcd's own watch returns the previous value here).
func TestCacheWatchPrevKVSlowConsumerLosesPrevKV(t *testing.T) {
	initialSnapshot := &clientv3.GetResponse{
		Header: &pb.ResponseHeader{Revision: 2},
		Kvs: []*mvccpb.KeyValue{
			{Key: []byte("/a"), Value: []byte("v2"), CreateRevision: 2, ModRevision: 2, Version: 1},
		},
	}
	mw := newMockWatcher(64)
	fakeClient := &clientv3.Client{Watcher: mw, KV: newKVStub(initialSnapshot)}
	c, err := New(fakeClient, "", WithHistoryWindowSize(4), WithPerWatcherBufferSize(64))
	if err != nil {
		t.Fatalf("New cache: %v", err)
	}
	defer c.Close()
	mw.triggerCreatedNotify()
	<-mw.registered
	ctx, cancel := context.WithTimeout(t.Context(), 5*time.Second)
	defer cancel()
	if err := c.WaitReady(ctx); err != nil {
		t.Fatalf("WaitReady: %v", err)
	}

	watchCh := c.Watch(ctx, "/a", clientv3.WithPrevKV())

	// Ten updates of /a, at revisions 3..12, each a modification (CreateRevision 2).
	// The first one alone, until the store has applied it (the store's own watcher
	// starts lagging and is caught up by the demux's resync), then the other nine.
	const last = 12
	put := func(rev int64) {
		mw.responses <- clientv3.WatchResponse{Events: []*clientv3.Event{{
			Type: clientv3.EventTypePut,
			Kv: &mvccpb.KeyValue{Key: []byte("/a"), Value: []byte(fmt.Sprintf("v%d", rev)),
				CreateRevision: 2, ModRevision: rev, Version: rev - 1},
		}}}
	}
	put(3)
	if err := c.WaitForRevision(ctx, 3); err != nil {
		t.Fatalf("WaitForRevision(3): %v", err)
	}
	for rev := int64(4); rev <= last; rev++ {
		put(rev)
	}
	if err := c.WaitForRevision(ctx, last); err != nil {
		t.Fatalf("WaitForRevision: %v (store at %d, demux at %d)", err, c.store.LatestRev(), c.demux.LatestRev())
	}

	missing := 0
	for rev := int64(3); rev <= last; rev++ {
		select {
		case <-ctx.Done():
			t.Fatalf("timed out at rev %d", rev)
		case resp := <-watchCh:
			if resp.Canceled {
				t.Fatalf("watch canceled at rev %d: %s", rev, resp.CancelReason)
			}
			for _, ev := range resp.Events {
				want := fmt.Sprintf("v%d", ev.Kv.ModRevision-1)
				switch {
				case ev.PrevKv == nil:
					missing++
					t.Logf("rev %d: PrevKv = nil, want value %q", ev.Kv.ModRevision, want)
				case string(ev.PrevKv.Value) != want:
					t.Errorf("rev %d: PrevKv.Value = %q, want %q", ev.Kv.ModRevision, ev.PrevKv.Value, want)
				}
			}
		}
	}
	if missing > 0 {
		t.Errorf("%d of %d update events delivered without PrevKv, and the watch was not canceled", missing, last-2)
	}
}

// waitForRev's context wakeup is a Broadcast on revCond from context.AfterFunc's
// goroutine, made without the store's lock: when it lands between the waiter's
// check of latest.rev and its Wait(), it is lost, and waitForRev sleeps until the
// store's revision next changes, ignoring the cancellation.
func TestStoreWaitForRevLostWakeup(t *testing.T) {
	s := newStore(32, 8)
	s.Restore(nil, 5)
	const iters = 200000
	for i := 0; i < iters; i++ {
		ctx, cancel := context.WithCancel(context.Background())
		done := make(chan error, 1)
		go func() { done <- s.waitForRev(ctx, 10) }()
		cancel()
		select {
		case <-done:
		case <-time.After(2 * time.Second):
			// Wake it so the test can finish, then report.
			s.mu.Lock()
			s.revCond.Broadcast()
			s.mu.Unlock()
			<-done
			t.Fatalf("iteration %d: waitForRev ignored its cancelled context for 2s (lost wakeup)", i)
		}
	}
}
