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

package apply

import (
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/zap/zaptest"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/client/pkg/v3/verify"
	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
	"go.etcd.io/etcd/server/v3/etcdserver/cindex"
	"go.etcd.io/etcd/server/v3/lease"
	"go.etcd.io/etcd/server/v3/storage/backend"
	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
	"go.etcd.io/etcd/server/v3/storage/mvcc"
	"go.etcd.io/etcd/server/v3/storage/schema"
)

// TestLeaseCheckpointCommittedWithConsistentIndex ensures that a backend commit
// that persists the consistent index of a lease checkpoint request also persists
// every checkpoint of the request.
func TestLeaseCheckpointCommittedWithConsistentIndex(t *testing.T) {
	// LockInsideApply checks that it is called from EtcdServer's applyEntries;
	// this test applies the request directly.
	revertFunc := verify.DisableVerifications()
	defer revertFunc()

	const checkpointIndex = 3
	lg := zaptest.NewLogger(t)
	var ci cindex.ConsistentIndexer
	var committed [][]int64
	bcfg := backend.DefaultBackendConfig(lg)
	bcfg.BatchLimit = 1 // commit at every Unlock with a pending write
	bcfg.Hooks = backend.NewHooks(func(tx backend.UnsafeReadWriter) {
		if ci == nil {
			return
		}
		ci.UnsafeSave(tx) // as the server's backend hooks do
		if index, _ := schema.UnsafeReadConsistentIndex(tx); index == checkpointIndex {
			committed = append(committed, []int64{
				schema.MustUnsafeGetLease(tx, 1).RemainingTTL,
				schema.MustUnsafeGetLease(tx, 2).RemainingTTL,
			})
		}
	})
	be, _ := betesting.NewTmpBackendFromCfg(t, bcfg)
	defer betesting.Close(t, be)

	cluster := membership.NewCluster(lg)
	lessor := lease.NewLessor(lg, be, cluster, lease.LessorConfig{CheckpointPersist: true})
	defer lessor.Stop()
	for _, id := range []lease.LeaseID{1, 2} {
		_, err := lessor.Grant(id, 600)
		require.NoError(t, err)
	}
	a := newApplierV3Backend(ApplierOptions{
		Logger:     lg,
		KV:         mvcc.NewStore(lg, be, lessor, mvcc.StoreConfig{}),
		Lessor:     lessor,
		Cluster:    cluster,
		RaftStatus: &fakeRaftStatusGetter{},
	})

	ci = cindex.NewConsistentIndex(be)
	// as EtcdServer's post-lock hook does
	be.SetTxPostLockInsideApplyHook(func() {
		applyingIdx, applyingTerm := ci.ConsistentApplyingIndex()
		if applyingIdx > ci.UnsafeConsistentIndex() {
			ci.SetConsistentIndex(applyingIdx, applyingTerm)
		}
	})
	ci.SetConsistentApplyingIndex(checkpointIndex, 1)
	_, err := a.LeaseCheckpoint(&pb.LeaseCheckpointRequest{Checkpoints: []*pb.LeaseCheckpoint{
		{ID: 1, Remaining_TTL: 100},
		{ID: 2, Remaining_TTL: 100},
	}})
	require.NoError(t, err)

	// Ensure every commit that persists the request's consistent index holds
	// both checkpoints.
	require.NotEmpty(t, committed)
	for _, remainingTTLs := range committed {
		require.Equalf(t, []int64{100, 100}, remainingTTLs, "remaining TTLs of leases 1 and 2 committed with consistent index %d", checkpointIndex)
	}
}
