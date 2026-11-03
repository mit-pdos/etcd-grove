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

package lease_test

import (
	"context"
	"sync/atomic"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/client/v3/leasing"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestLeasingDeleteRangeRevokeWatchCompacted checks that a range delete does
// not proceed while another client still holds the lease on a key in the
// range, when the watch waiting for that lease to be released ends without
// seeing its deletion (here, its start revision is compacted).
func TestLeasingDeleteRangeRevokeWatchCompacted(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 1})
	defer clus.Terminate(t)

	cliA, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints()})
	require.NoError(t, err)
	defer cliA.Close()
	cliB, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(0).Endpoints()})
	require.NoError(t, err)
	defer cliB.Close()

	_, err = clus.Client(0).Put(t.Context(), "k", "v1")
	require.NoError(t, err)

	// A's lease monitor does not see the revoke until B watches again.
	gate := make(chan struct{})
	cliA.Watcher = &gatedWatcher{Watcher: cliA.Watcher, gate: gate}
	lkvA, closeA, err := leasing.NewKV(cliA, "pfx/")
	require.NoError(t, err)
	defer closeA()
	cw := &compactingWatcher{Watcher: cliB.Watcher, kv: clus.Client(0), onSecond: func() { close(gate) }}
	cliB.Watcher = cw
	lkvB, closeB, err := leasing.NewKV(cliB, "pfx/")
	require.NoError(t, err)
	defer closeB()

	// A acquires the lease on k and caches it.
	resp, err := lkvA.Get(t.Context(), "k")
	require.NoError(t, err)
	require.Len(t, resp.Kvs, 1)

	// B's range delete revokes A's lease; the watch waiting for A to release it
	// is compacted.
	cw.armed.Store(true)
	ctx, cancel := context.WithTimeout(t.Context(), 10*time.Second)
	defer cancel()
	_, err = lkvB.Delete(ctx, "k", clientv3.WithPrefix())
	require.NoError(t, err)
	cw.armed.Store(false)
	require.GreaterOrEqualf(t, cw.calls.Load(), int32(1), "expected B to wait for A's lease to be released")

	etcdResp, err := clus.Client(0).Get(t.Context(), "k")
	require.NoError(t, err)
	require.Emptyf(t, etcdResp.Kvs, "expected k deleted on etcd")
	resp, err = lkvA.Get(t.Context(), "k")
	require.NoError(t, err)
	require.Emptyf(t, resp.Kvs, "expected A's leasing KV not to return k, deleted on etcd, got %+v", resp.Kvs)
}

// gatedWatcher starts its watches only once gate is closed.
type gatedWatcher struct {
	clientv3.Watcher
	gate <-chan struct{}
}

func (w *gatedWatcher) Watch(ctx context.Context, key string, opts ...clientv3.OpOption) clientv3.WatchChan {
	select {
	case <-w.gate:
		return w.Watcher.Watch(ctx, key, opts...)
	case <-ctx.Done():
		ch := make(chan clientv3.WatchResponse)
		close(ch)
		return ch
	}
}

// compactingWatcher, when armed, compacts etcd past the start revision of the
// first watch it is asked for, so that watch is canceled; it calls onSecond
// when asked for a second watch.
type compactingWatcher struct {
	clientv3.Watcher
	kv       clientv3.KV
	onSecond func()
	armed    atomic.Bool
	calls    atomic.Int32
}

func (w *compactingWatcher) Watch(ctx context.Context, key string, opts ...clientv3.OpOption) clientv3.WatchChan {
	if w.armed.Load() {
		switch w.calls.Add(1) {
		case 1:
			w.kv.Put(ctx, "unrelated", "1")
			if resp, err := w.kv.Put(ctx, "unrelated", "2"); err == nil {
				w.kv.Compact(ctx, resp.Header.Revision)
			}
		case 2:
			w.onSecond()
		}
	}
	return w.Watcher.Watch(ctx, key, opts...)
}
