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
	"sync/atomic"
	"testing"
	"time"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	clientv3 "go.etcd.io/etcd/client/v3"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

// TestV3LeaseAuthDuringSnapshotRestore: with auth enabled, a user who may not
// read the key attached to a lease is refused LeaseLeases and LeaseTimeToLive
// with keys. While a follower applies a snapshot, the lessor is recovered
// (every lease with no key attached) before the key-value store is restored
// and re-attaches the keys; both permission checks read the follower's lessor
// in that window and pass. LeaseLeases then answers; LeaseTimeToLive with
// keys is forwarded to the leader, which returns the key itself.
//
// No failpoint: the window is the key-value store's index restore, widened by
// many keys in the store.
func TestV3LeaseAuthDuringSnapshotRestore(t *testing.T) {
	integration.BeforeTest(t)

	clus := integration.NewCluster(t, &integration.ClusterConfig{Size: 3, SnapshotCount: 100, SnapshotCatchUpEntries: 10})
	defer clus.Terminate(t)

	leadIdx := clus.WaitLeader(t)
	fIdx := (leadIdx + 1) % 3

	authSetupRoot(t, integration.ToGRPC(clus.Client(leadIdx)).Auth)
	rootc, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(leadIdx).Endpoints(), Username: "root", Password: "123"})
	require.NoError(t, err)
	defer rootc.Close()

	ctx, cancel := context.WithTimeout(t.Context(), 5*time.Minute)
	defer cancel()

	// u may read and write "a/" only.
	_, err = rootc.UserAdd(ctx, "u", "u-pw")
	require.NoError(t, err)
	_, err = rootc.RoleAdd(ctx, "ra")
	require.NoError(t, err)
	_, err = rootc.RoleGrantPermission(ctx, "ra", "a/", clientv3.GetPrefixRangeEnd("a/"), clientv3.PermissionType(clientv3.PermReadWrite))
	require.NoError(t, err)
	_, err = rootc.UserGrantRole(ctx, "u", "ra")
	require.NoError(t, err)

	// root's lease Lz holds z/lease.
	lz, err := rootc.Grant(ctx, 9000)
	require.NoError(t, err)
	_, err = rootc.Put(ctx, "z/lease", "v", clientv3.WithLease(lz.ID))
	require.NoError(t, err)

	// Many keys, so that restoring the store's index takes a while.
	const txns, opsPerTxn = 1500, 128
	for i := 0; i < txns; i++ {
		ops := make([]clientv3.Op, 0, opsPerTxn)
		for j := 0; j < opsPerTxn; j++ {
			ops = append(ops, clientv3.OpPut(fmt.Sprintf("p/%06d/%03d", i, j), "v"))
		}
		_, err = rootc.Txn(ctx).Then(ops...).Commit()
		require.NoError(t, err)
	}

	uc, err := integration.NewClient(t, clientv3.Config{Endpoints: clus.Client(fIdx).Endpoints(), Username: "u", Password: "u-pw"})
	require.NoError(t, err)
	defer uc.Close()

	// Before: once the follower F holds z/lease on Lz, u is refused both.
	require.Eventually(t, func() bool {
		_, e1 := uc.TimeToLive(ctx, lz.ID, clientv3.WithAttachedKeys())
		_, e2 := uc.Leases(ctx)
		return e1 != nil && e2 != nil
	}, 10*time.Second, 50*time.Millisecond)
	_, err = uc.Get(ctx, "z/lease")
	require.Error(t, err, "u may not read z/lease")

	// Partition F, write past the leader's log compaction, heal: F applies a snapshot.
	f := clus.Members[fIdx]
	var others []*integration.Member
	for i, m := range clus.Members {
		if i != fIdx {
			others = append(others, m)
		}
	}
	f.InjectPartition(t, others...)
	for i := 0; i < 300; i++ {
		_, err = rootc.Put(ctx, fmt.Sprintf("q/%d", i), "v")
		require.NoError(t, err)
	}

	// u calls Leases and TimeToLive with keys at F, in a loop, through the heal.
	var (
		stop                    atomic.Bool
		mu                      sync.Mutex
		leasesPassed, ttlPassed int
		ttlKeys                 []string
		leasesSeen              []int64
		wg                      sync.WaitGroup
	)
	for g := 0; g < 2; g++ {
		wg.Add(2)
		go func() {
			defer wg.Done()
			for !stop.Load() {
				cctx, ccancel := context.WithTimeout(ctx, 2*time.Second)
				r, e := uc.Leases(cctx)
				ccancel()
				if e == nil {
					mu.Lock()
					leasesPassed++
					for _, l := range r.Leases {
						leasesSeen = append(leasesSeen, int64(l.ID))
					}
					mu.Unlock()
					t.Logf("Leases at F answered u: %d leases", len(r.Leases))
					return
				}
			}
		}()
		go func() {
			defer wg.Done()
			for !stop.Load() {
				cctx, ccancel := context.WithTimeout(ctx, 2*time.Second)
				r, e := uc.TimeToLive(cctx, lz.ID, clientv3.WithAttachedKeys())
				ccancel()
				if e == nil {
					mu.Lock()
					ttlPassed++
					for _, k := range r.Keys {
						ttlKeys = append(ttlKeys, string(k))
					}
					mu.Unlock()
					t.Logf("TimeToLive(Lz, keys) at F answered u: keys %q", r.Keys)
					return
				}
			}
		}()
	}
	f.RecoverPartition(t, others...)
	time.Sleep(20 * time.Second)
	stop.Store(true)
	wg.Wait()

	t.Logf("Leases at F not refused %d times (lease IDs returned: %d, Lz=%x)", leasesPassed, len(leasesSeen), lz.ID)
	if len(ttlKeys) > 5 {
		t.Logf("TimeToLive(Lz, keys) at F not refused %d times; first keys returned: %v", ttlPassed, ttlKeys[:5])
	} else {
		t.Logf("TimeToLive(Lz, keys) at F not refused %d times; keys returned: %v", ttlPassed, ttlKeys)
	}
	assert.Zero(t, leasesPassed, "Leases answered a user who may not read a key attached to a listed lease")
	assert.NotContains(t, ttlKeys, "z/lease", "TimeToLive with keys returned a key the caller may not read")
	assert.Zero(t, ttlPassed, "TimeToLive with keys answered a user who may not read the lease's key")
}
