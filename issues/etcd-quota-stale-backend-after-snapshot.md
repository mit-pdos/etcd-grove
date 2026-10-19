---
upstream: none
checked: 2026-10-19
links:
  - etcd-io/etcd#17318 issue closed: NOSPACE alarm not clearing after the db shrank; no snapshot detail, cause not shown
candidate: issues/upstream/etcd-quota-stale-backend-after-snapshot/
---

# After a member installs a leader's snapshot, its gRPC quota check still measures the old, closed backend

- **Status**: a bug (a wrong result, then a cluster-wide loss of write availability), reproduced
  by an integration test at the pin; reachable with the default configuration through normal
  operations (a lagging member caught up by a snapshot, then the documented NOSPACE recovery).
- **Where**: at the etcd pin of `etc/goose.py` (`8a24be2a3`):
  `server/etcdserver/api/v3rpc/quota.go:53-95`: `NewQuotaKVServer`/`NewQuotaLeaseServer` build
  their `quotaAlarmer` from `newBackendQuota(s, …)`, which calls
  `storage.NewBackendQuota(…, s.Backend(), name)` once, when the gRPC server is built
  (`v3rpc/grpc.go:80-82`; also `v3client.go:33-36`); `storage.BackendQuota.Available`
  (`server/storage/quota.go`) then reads `b.be.Size()` of that backend forever.
  `server/etcdserver/server.go:1011-1159` (`applySnapshot`) replaces `s.be` by the snapshot's
  backend (`s.be = newbe`, `:1093`) and closes the old one in a goroutine; it rebuilds the apply
  chain (`s.uberApply = s.NewUberApplier()`, `:1158`, whose `quotaApplierV3` takes the new
  `s.be`), but not the gRPC quota servers. `backend.Size()` (`backend/backend.go:455`) is an
  atomic updated only at commits, so a closed backend's size is frozen.
- **What happens**: after a snapshot install, every `Put`/`Txn`/`LeaseGrant` the member receives
  is checked against the old backend's last size. If that size was over `--quota-backend-bytes`
  (the member's db had grown past the quota before it fell behind), every mutating request to
  the member is refused with `ErrGRPCNoSpace`, and each refusal proposes a NOSPACE alarm
  activation (`quotaAlarmer.check`, `quota.go:40-51`), which, once applied, makes **every** member
  refuse writes. Compacting, defragmenting (which works on the new backend) and disarming do not
  help: the next write through that member raises the alarm again. Only a restart of the member
  clears it. The documented recovery from NOSPACE (compact, defragment every member, disarm) thus
  fails whenever a member that was down during it catches up by a snapshot. In the other
  direction (old db small, new db over quota) the gRPC check of that member never refuses; the
  apply path's quota (rebuilt with the new backend) still raises the alarm, so that direction is
  only a missed early refusal.

  Reproduction (`tests/integration`, run at the pin: two runs failed at the last assertion, a
  third failed earlier, in the setup's disarm step; with the fix below it passes 3 of 3):

```go
package integration

import (
	"os"
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

func TestV3QuotaCheckAfterSnapshotInstall(t *testing.T) {
	integration.BeforeTest(t)
	quotasize := int64(16 * os.Getpagesize())

	clus := integration.NewCluster(t, &integration.ClusterConfig{
		Size: 3, SnapshotCount: 10, SnapshotCatchUpEntries: 5,
	})
	defer clus.Terminate(t)

	// A quota on member 2 only.
	clus.Members[2].QuotaBackendBytes = quotasize
	clus.Members[2].Stop(t)
	require.NoError(t, clus.Members[2].Restart(t))
	clus.WaitMembersForLeader(t, clus.Members)

	// Grow every member's db past member 2's quota (through member 0, which has none).
	kvc0 := integration.ToGRPC(clus.Client(0)).KV
	waitForRestart(t, kvc0)
	_, err := kvc0.Put(t.Context(), &pb.PutRequest{Key: []byte("big"), Value: make([]byte, quotasize)})
	require.NoError(t, err)
	time.Sleep(time.Second)
	require.Greater(t, clus.Members[2].Server.Backend().Size(), quotasize)
	// Member 2's apply raises the NOSPACE alarm; wait for it.
	for i := 0; ; i++ {
		alarms, aerr := clus.Members[0].Server.Alarm(t.Context(), &pb.AlarmRequest{Action: pb.AlarmRequest_GET})
		require.NoError(t, aerr)
		if len(alarms.Alarms) > 0 {
			break
		}
		require.Less(t, i, 100, "no alarm")
		time.Sleep(50 * time.Millisecond)
	}

	// Member 2 goes down; the others recover from NOSPACE: disarm, delete, compact, defragment.
	clus.Members[2].Stop(t)
	alarms, err := clus.Members[0].Server.Alarm(t.Context(), &pb.AlarmRequest{Action: pb.AlarmRequest_GET})
	require.NoError(t, err)
	for _, a := range alarms.Alarms {
		_, err = clus.Members[0].Server.Alarm(t.Context(), &pb.AlarmRequest{
			Action: pb.AlarmRequest_DEACTIVATE, MemberID: a.MemberID, Alarm: a.Alarm})
		require.NoError(t, err)
	}
	_, err = kvc0.DeleteRange(t.Context(), &pb.DeleteRangeRequest{Key: []byte("big")})
	require.NoError(t, err)
	for i := 0; i < 40; i++ {
		_, err = kvc0.Put(t.Context(), &pb.PutRequest{Key: []byte("k"), Value: []byte("v")})
		require.NoError(t, err)
	}
	rev, err := kvc0.Range(t.Context(), &pb.RangeRequest{Key: []byte("k")})
	require.NoError(t, err)
	_, err = kvc0.Compact(t.Context(), &pb.CompactionRequest{Revision: rev.Header.Revision, Physical: true})
	require.NoError(t, err)
	for i := 0; i < 2; i++ {
		require.NoError(t, clus.Members[i].Server.Backend().Defrag())
	}
	for i := 0; i < 40; i++ { // the leader snapshots and compacts its raft log past member 2
		_, err = kvc0.Put(t.Context(), &pb.PutRequest{Key: []byte("k"), Value: []byte("v")})
		require.NoError(t, err)
	}

	// Member 2 restarts and catches up by the leader's (defragmented) snapshot.
	require.NoError(t, clus.Members[2].Restart(t))
	clus.WaitMembersForLeader(t, clus.Members)
	kvc2 := integration.ToGRPC(clus.Client(2)).KV
	waitForRestart(t, kvc2)
	integration.WaitClientV3(t, clus.Members[2].Client)
	deadline := time.Now().Add(10 * time.Second)
	for clus.Members[2].Server.Backend().Size() >= quotasize && time.Now().Before(deadline) {
		time.Sleep(100 * time.Millisecond)
	}
	sz2 := clus.Members[2].Server.Backend().Size()
	require.Less(t, sz2, quotasize, "member 2 did not install the leader's snapshot")

	// Member 2's db is under its quota: a small put through it should succeed.
	_, err = kvc2.Put(t.Context(), &pb.PutRequest{Key: []byte("after"), Value: []byte("x")})
	require.NoErrorf(t, err, "put through member 2 after its snapshot install (db %d < quota %d)", sz2, quotasize)
}
```

  Observed (two of the runs): member 2's db after catching up is 28-32 KiB under a 64 KiB quota;
  the put fails with `etcdserver: mvcc: database space exceeded`; one second later the alarm list
  holds `NOSPACE` for member 2, and a put through member 0 (db 28 KiB, no quota) fails the same
  way (every member's apply logs `no space`).
- **Expected**: the gRPC quota check measures the member's current backend, as the apply path's
  quota does after `applySnapshot` rebuilds it; nothing documents that a member keeps judging
  writes by a backend it closed.
- **How the proof handles it**: not yet: today no member installs a snapshot (`bootOk`'s
  `"%Hnosnap"`, D21 M3), and `applySnapshot`'s spec covers only the empty snapshot
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applySnapshot.lean`). Track T-S
  (`notes/decisions.md`, D22, decision D22g) states the quota's contract over the backend
  captured at construction (closed or not) rather than the current one.
- **Possible fixes**: make `newBackendQuota` read `s.Backend()` at each check. Tested at the pin
  (the test above passes 3 of 3):

```go
func newBackendQuota(s *etcdserver.EtcdServer, name string) storage.Quota {
	return &serverQuota{s: s, name: name}
}

// serverQuota measures the server's current backend: applySnapshot replaces it.
type serverQuota struct {
	s    *etcdserver.EtcdServer
	name string
}

func (q *serverQuota) cur() storage.Quota {
	return storage.NewBackendQuota(q.s.Logger(), q.s.Cfg.QuotaBackendBytes, q.s.Backend(), q.name)
}

func (q *serverQuota) Available(req any) bool { return q.cur().Available(req) }
func (q *serverQuota) Cost(req any) int        { return q.cur().Cost(req) }
func (q *serverQuota) Remaining() int64        { return q.cur().Remaining() }
```

  (A version that does not rebuild the `BackendQuota` per call would keep the configured size
  and read only `s.Backend().Size()`.)
- **Found**: 2026-10-19, scoping track T-S (the snapshot path), reading `applySnapshot`'s
  backend swap against the holders of `s.Backend()`.
