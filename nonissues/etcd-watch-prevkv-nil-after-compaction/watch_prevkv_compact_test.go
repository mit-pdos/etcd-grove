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

package integration

import (
	"context"
	"fmt"
	"sync"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestWatchPrevKVAfterCompaction: a watch with WithPrevKV gives an event that is not a creation
// its previous key-value only if that is not compacted by the time the server sends the event.
// Here the watches fall behind the writes (many watches on one stream, as one client's watches
// share it), and a compaction at the latest revision is applied while events below it are still
// queued on the server: those events reach the client as modifications (or deletions) with a nil
// PrevKv, before (or without) any cancellation telling the client the watch was compacted.
func TestWatchPrevKVAfterCompaction(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)
	cli := clus.Client(0)
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
	defer cancel()

	const (
		nkeys    = 50  // keys under the prefix, all created before the watches
		nwatches = 100 // watches on the prefix, on one gRPC stream (same context)
		nwriters = 16
		nputs    = 2000 // overwrites of existing keys: every event is a modification
	)
	key := func(i int) string { return fmt.Sprintf("/registry/pods/p%03d", i%nkeys) }
	for i := 0; i < nkeys; i++ {
		_, err := cli.Put(ctx, key(i), "v0")
		require.NoError(t, err)
	}

	wctx, wcancel := context.WithCancel(ctx)
	defer wcancel()
	wchs := make([]clientv3.WatchChan, nwatches)
	for i := range wchs {
		wchs[i] = cli.Watch(wctx, "/registry/pods/", clientv3.WithPrefix(), clientv3.WithPrevKV(), clientv3.WithCreatedNotify())
		wr := <-wchs[i]
		require.True(t, wr.Created, "watch %d: expected a created response, got %+v", i, wr)
	}

	var wg sync.WaitGroup
	for w := 0; w < nwriters; w++ {
		wg.Add(1)
		go func(w int) {
			defer wg.Done()
			for i := w; i < nputs; i += nwriters {
				if _, err := cli.Put(ctx, key(i), fmt.Sprintf("v%d", i+1)); err != nil {
					t.Errorf("put: %v", err)
					return
				}
			}
		}(w)
	}
	wg.Wait()
	resp, err := cli.Get(ctx, "/registry/pods/", clientv3.WithPrefix(), clientv3.WithCountOnly())
	require.NoError(t, err)
	last := resp.Header.Revision
	// A compaction at the current revision, as a periodic compactor runs it.
	_, err = cli.Compact(ctx, last)
	require.NoError(t, err)

	type miss struct {
		watch   int
		live    bool // the watch was never canceled
		key     string
		modRev  int64
		evType  string
		compact int64
	}
	var mu sync.Mutex
	var misses []miss
	total, canceled := 0, 0
	var rg sync.WaitGroup
	for i, wch := range wchs {
		rg.Add(1)
		go func(i int, wch clientv3.WatchChan) {
			defer rg.Done()
			var mine []miss
			defer func() {
				mu.Lock()
				misses = append(misses, mine...)
				mu.Unlock()
			}()
			for wr := range wch {
				mu.Lock()
				if wr.Canceled {
					// Canceled as compacted: the client knows it missed events.
					canceled++
					mu.Unlock()
					for j := range mine {
						mine[j].live = false
					}
					return
				}
				for _, ev := range wr.Events {
					total++
					if !ev.IsCreate() && ev.PrevKv == nil {
						mine = append(mine, miss{i, true, string(ev.Kv.Key), ev.Kv.ModRevision, ev.Type.String(), last})
					}
				}
				mu.Unlock()
				if n := len(wr.Events); n > 0 && wr.Events[n-1].Kv.ModRevision >= last {
					return
				}
			}
			t.Errorf("watch %d: closed before revision %d", i, last)
		}(i, wch)
	}
	rg.Wait()

	if len(misses) > 0 {
		live := 0
		m := misses[0]
		for _, x := range misses {
			if x.live {
				if live == 0 {
					m = x
				}
				live++
			}
		}
		t.Errorf("watch %d: %s event of existing key %q at revision %d has no PrevKv (compaction at %d, applied after the event)",
			m.watch, m.evType, m.key, m.modRev, m.compact)
		t.Errorf("%d of %d events from %d watches with WithPrevKV (%d canceled as compacted) had a nil PrevKv, %d of them on watches never canceled", len(misses), total, nwatches, canceled, live)
	}
}
