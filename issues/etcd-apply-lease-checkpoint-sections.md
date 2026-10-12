# server/etcdserver/apply: a lease checkpoint entry writes the backend in one critical section per checkpoint

- **Status**: open (low impact: a remaining TTL lost across a crash; not filed).
- **Where**: `server/etcdserver/apply/backend.go` at bc8b52a50 (`etc/goose.py`'s etcd pin),
  `applierV3backend.LeaseCheckpoint` (`backend.go:97-105`): it calls `Lessor.Checkpoint` once
  per checkpoint of the request; `lessor.Checkpoint` (`server/lease/lessor.go:367-383`) persists
  the lease (`Lease.persistTo`, `server/lease/lease.go:55-61`) when checkpoints are persisted
  (`CheckpointPersist`, or a cluster version at least 3.6), each in its own
  `BatchTx().LockInsideApply()` ... `Unlock()`. The checkpoint scheduler proposes up to
  `maxLeaseCheckpointBatchSize` (1000) checkpoints per request (`lessor.go:55`, `:674`).
- **What happens**: the consistent-index protocol of the apply loop (the server's
  `txPostLockInsideApplyHook`, `server.go:2448-2455`, sets the consistent index to the entry
  being applied under the batch lock, right before the entry's writes) assumes an entry's
  writes are made in one critical section: a backend commit, which takes the same lock
  (periodic, `backend.go:465`, or at `Unlock` past the batch limit, `batch_tx.go:355`), then
  persists the entry's index with all of its writes or none. A checkpoint request with `n`
  checkpoints makes `n` critical sections: a commit between two of them persists the entry's
  index with only the first checkpoints' remaining TTLs; after a crash at that point the entry is
  not applied again (it is at or below the persisted index), so the other leases keep their older
  persisted remaining TTL (or their full TTL), the checkpoint's effect lost. Reproduction (the
  hook counts the critical sections; `server/etcdserver/apply/`, next to
  `uber_applier_test.go`; it passes, asserting the two sections):

  ```go
  package apply

  import (
  	"testing"
  	"time"

  	"github.com/stretchr/testify/require"
  	"go.uber.org/zap/zaptest"
  	"golang.org/x/crypto/bcrypt"

  	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
  	"go.etcd.io/etcd/server/v3/auth"
  	"go.etcd.io/etcd/server/v3/etcdserver/api/membership"
  	"go.etcd.io/etcd/server/v3/etcdserver/api/v3alarm"
  	"go.etcd.io/etcd/server/v3/etcdserver/cindex"
  	"go.etcd.io/etcd/server/v3/lease"
  	betesting "go.etcd.io/etcd/server/v3/storage/backend/testing"
  	"go.etcd.io/etcd/server/v3/storage/mvcc"
  	"go.etcd.io/etcd/server/v3/storage/schema"
  )

  // A LeaseCheckpoint entry with two checkpoints writes the backend in two critical sections of
  // the batch lock: the post-lock hook runs once per checkpoint.
  func TestLeaseCheckpointCriticalSections(t *testing.T) {
  	lg := zaptest.NewLogger(t)
  	be, _ := betesting.NewDefaultTmpBackend(t)
  	t.Cleanup(func() { betesting.Close(t, be) })
  	cluster := membership.NewCluster(lg)
  	cluster.SetBackend(schema.NewMembershipBackend(lg, be))
  	cluster.AddMember(&membership.Member{ID: memberID}, true)
  	// checkpoints persisted (as with a cluster version >= 3.6)
  	lessor := lease.NewLessor(lg, be, cluster, lease.LessorConfig{CheckpointPersist: true})
  	kv := mvcc.NewStore(lg, be, lessor, mvcc.StoreConfig{})
  	alarmStore, err := v3alarm.NewAlarmStore(lg, schema.NewAlarmBackend(lg, be))
  	require.NoError(t, err)
  	tp, err := auth.NewTokenProvider(lg, "simple", dummyIndexWaiter, 300*time.Second)
  	require.NoError(t, err)
  	authStore := auth.NewAuthStore(lg, schema.NewAuthBackend(lg, be), tp, bcrypt.DefaultCost)
  	ua := NewUberApplier(ApplierOptions{
  		Logger: lg, KV: kv, AlarmStore: alarmStore, AuthStore: authStore, Lessor: lessor,
  		Cluster: cluster, RaftStatus: &fakeRaftStatusGetter{}, SnapshotServer: &fakeSnapshotServer{},
  		ConsistentIndex: cindex.NewConsistentIndex(be), Backend: be,
  		QuotaBackendBytesCfg: 16 * 1024 * 1024, WarningApplyDuration: time.Hour,
  	})
  	apply := func(r *pb.InternalRaftRequest) *Result {
  		r.Header = &pb.RequestHeader{}
  		return ua.Apply(&InternalRaftRequestWrapper{InternalRaftRequest: r}, membership.ApplyBoth)
  	}
  	for _, id := range []int64{1, 2} {
  		res := apply(&pb.InternalRaftRequest{LeaseGrant: &pb.LeaseGrantRequest{ID: id, TTL: 600}})
  		require.NoError(t, res.Err)
  	}

  	sections := 0
  	be.SetTxPostLockInsideApplyHook(func() { sections++ })
  	res := apply(&pb.InternalRaftRequest{Put: &pb.PutRequest{Key: []byte("k"), Value: []byte("v")}})
  	require.NoError(t, res.Err)
  	require.Equal(t, 1, sections, "a put: one critical section")

  	sections = 0
  	res = apply(&pb.InternalRaftRequest{LeaseCheckpoint: &pb.LeaseCheckpointRequest{
  		Checkpoints: []*pb.LeaseCheckpoint{{ID: 1, Remaining_TTL: 100}, {ID: 2, Remaining_TTL: 100}},
  	}})
  	require.NoError(t, res.Err)
  	require.Equal(t, 2, sections, "a checkpoint request with two checkpoints: two critical sections")
  }
  ```
- **Expected**: an applied entry's backend writes are atomic with its consistent index (what
  `txPostLockInsideApplyHook` is for, etcd's #13766): after a crash, an entry at or below the
  persisted index has all of its effects in the backend.
- **How the proof handles it**: the backend applier's `LeaseCheckpoint` triple takes a request
  with at most one checkpoint (`applierV3backend__LeaseCheckpoint.lean`, the premise
  `cms.length ≤ 1`; `rqOk` of `Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/Chain.lean`, which
  the apply package's `dispatch` will take, unit 2): the critical-section contract
  (`csContract`, the apply thread's protocol: one section, the hook first) is spent by the
  first checkpoint's write, and the protocol (`hook_set_au`, the entry `p + 1`) has no step for a
  second section of the same entry.
- **Possible fixes**: persist the checkpoints of a request in one critical section (a lessor
  method taking the batch, `CheckpointBatch(cps)`, locking `LockInsideApply` once and putting
  every lease); or let `persistTo` take an already locked batch transaction from the applier.
- **Found**: 2026-10-12, apply unit 1 (the backend applier's `LeaseCheckpoint` against the
  lessor's `Checkpoint` contract), reproduced with the test above at bc8b52a50.
