---
upstream: unchecked
checked: 2026-10-26
links: []
---

# After a member installs a leader's snapshot, its applied index stays at the old value and it refuses every write with "too many requests"

- **Status**: a bug (a loss of write availability through one member, lasting until some other
  member's write commits; plus stale status fields), reproduced by an integration test at the pin.
  Reachable with the default configuration: a follower that falls behind the leader's raft log
  compaction and is caught up by a snapshot, in a cluster that is then quiet.
- **Where**: at the etcd pin of `etc/goose.py` (`bc9c3868c`), `server/etcdserver/`:
  - `server.go:1014-1172` (`applySnapshot`) moves `ep.appliedi`/`ep.appliedt` to the snapshot's
    index and term (`:1164-1168`) but never calls `setAppliedIndex` (nor `setTerm`). The only
    writers of the atomic `s.appliedIndex` (`:215`, `setAppliedIndex` `:1707`) are `apply`'s two
    cases (`:1937`, `:1945`). Nor is it initialized at start: `run` sets `ep.appliedi` to the
    snapshot's index (`:801-807`), the atomic stays 0. `applyAll` (`:978-985`) triggers `applyWait`
    at `ep.appliedi`, so `applyWait` is up to date; only the atomic lags.
  - `v3_server.go:1059-1064` (`processInternalRaftRequestOnce`, every proposal: `Put`, `Txn`,
    `DeleteRange`, `LeaseGrant`, `LeaseRevoke`, auth and member-attribute requests, ...) refuses
    with `ErrTooManyRequests` when `exceedsRequestLimit(getAppliedIndex(), getCommittedIndex())`,
    i.e. committed > applied + 5000 (`util.go:60-70`; `maxGapBetweenApplyAndCommitIndex`,
    `v3_server.go:50-52`). `updateCommittedIndex` raises the committed index to the snapshot's
    index (`raft.go:350-361`).
  - A leader sends a snapshot only to a follower below its compacted log, and compacts to
    `appliedi - SnapshotCatchUpEntries` (`server.go:2155-2172`, default 5000); the merged snapshot
    is taken at the leader's `ep.appliedi` (`snapshot_merge.go:32-46`, called at `server.go:1007`).
    So the snapshot index exceeds the follower's applied index by more than 5000 whenever
    `SnapshotCatchUpEntries ≥ 5000` (the default): after every snapshot install, the limit trips.
    In a quiet cluster the leader's last index is the snapshot's index, so no entry follows it.
- **What happens**: from the snapshot install until the next entry is applied on that member,
  every write proposed through it fails with `etcdserver: too many requests`; the member's own
  proposals cannot clear it (they are refused before reaching raft). Writes through another
  member, or anything the leader proposes (a lease expiry, a periodic compaction, a new term's
  empty entry), commit an entry above the snapshot, whose `apply` raises the atomic past the gap.
  In a cluster where clients reach only that member (a client pinned to one endpoint) and nothing
  else writes, the member refuses writes indefinitely. Also stale meanwhile: `Status`'s
  `RaftAppliedIndex` (`api/v3rpc/maintenance.go:278`, shown by `etcdctl endpoint status`) and
  `RaftTerm` in response headers and `Status` (`Term()`, `server.go:1763`; `api/v3rpc/header.go:59`,
  `maintenance.go:279`, `v3_server.go:731`), which keep the pre-snapshot values; after a restart
  `RaftAppliedIndex` is 0 until an entry is applied.

  Readers that are *not* affected: `waitAppliedIndex` (`v3_server.go:458-467`, used by
  `LeaseRenew`, `leaseTimeToLive`, `isLearnerReady` `server.go:1579`) waits on
  `ApplyWaitCommit` = `applyWait.Wait(committedIndex)` (`server.go:628-630`), i.e. on `applyWait`,
  which `applyAll` triggered at the snapshot index, not on the atomic. The linearizable read loop
  (`read/read.go:130-139`) compares the atomic with the read index and, when it is lower, waits on
  `ApplyWait(confirmedIndex)` (again `applyWait`, already triggered): a stale low atomic only costs
  an extra, immediately-ready wait; reads stay correct and live.

  Reproduction (`tests/integration`, run at the pin with `GOTOOLCHAIN=go1.27.1`: fails, 2 runs of 2;
  with the fix below it passes):

```go
package integration

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"

	pb "go.etcd.io/etcd/api/v3/etcdserverpb"
	"go.etcd.io/etcd/tests/v3/framework/integration"
)

func TestAppliedIndexStaleAfterSnapshotInstall(t *testing.T) {
	integration.BeforeTest(t)
	clus := integration.NewCluster(t, &integration.ClusterConfig{
		Size: 3, SnapshotCount: 100, SnapshotCatchUpEntries: 5,
	})
	defer clus.Terminate(t)

	lead := clus.WaitLeader(t)
	f := (lead + 1) % 3
	var others []*integration.Member
	for i := range clus.Members {
		if i != f {
			others = append(others, clus.Members[i])
		}
	}
	clus.Members[f].InjectPartition(t, others...)

	kvl := integration.ToGRPC(clus.Client(lead)).KV
	for i := 0; i < 5200; i++ {
		_, err := kvl.Put(t.Context(), &pb.PutRequest{Key: []byte("k"), Value: []byte("v")})
		require.NoError(t, err)
	}
	ls := clus.Members[lead].Server

	clus.Members[f].RecoverPartition(t, others...)
	fs := clus.Members[f].Server
	deadline := time.Now().Add(20 * time.Second)
	for fs.CommittedIndex() < ls.CommittedIndex() && time.Now().Before(deadline) {
		time.Sleep(100 * time.Millisecond)
	}
	time.Sleep(2 * time.Second) // let applySnapshot finish
	require.Equal(t, ls.CommittedIndex(), fs.CommittedIndex(), "follower did not catch up")

	kvf := integration.ToGRPC(clus.Client(f)).KV
	var errs []error
	for i := 0; i < 5; i++ {
		_, err := kvf.Put(t.Context(), &pb.PutRequest{Key: []byte("after"), Value: []byte("x")})
		t.Logf("put through follower: %v (applied %d committed %d)", err, fs.AppliedIndex(), fs.CommittedIndex())
		errs = append(errs, err)
		time.Sleep(2 * time.Second)
	}
	// One write through another member: its entry, applied on the follower after the
	// snapshot, raises the follower's appliedIndex.
	_, err := kvl.Put(t.Context(), &pb.PutRequest{Key: []byte("other"), Value: []byte("x")})
	require.NoError(t, err)
	time.Sleep(time.Second)
	_, err = kvf.Put(t.Context(), &pb.PutRequest{Key: []byte("after"), Value: []byte("x")})
	require.NoError(t, err)
	for _, err := range errs {
		require.NoError(t, err, "put through the follower after its snapshot install")
	}
}
```

  Observed: the follower reports applied 8, committed 5208 (the leader: 5208, 5208); all five puts
  through it over 10 seconds fail with `rpc error: code = Unknown desc = etcdserver: too many
  requests`; after one put through the leader, the follower's applied index is 5210 and its put
  succeeds.
- **Expected**: the applied index the server publishes (`AppliedIndex()`, the request limit,
  `Status`) is the index the member has applied, which after `applySnapshot` is the snapshot's;
  a member that has fully caught up does not refuse writes as overloaded.
- **How the proof handles it**: not yet: no member installs a snapshot in the current proof
  (`applySnapshot`'s spec covers only the empty snapshot), and `srvAppliedInv`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRequest.lean`) ties the atomic to the ghost
  applied index `γr.applied` exactly; with snapshots it has to weaken to "atomic ≤ applied" (or
  the fix below must be in the verified code). Decided (D22 J0, 2026-10-26): the verified code keeps
  Go's behavior and the invariant becomes "atomic ≤ ghost" (stage J5; `notes/snapshot-sj-plan.md`,
  "J0 decisions", item 4).
- **Possible fixes**: at the end of `applySnapshot`, after the `ep` updates:

```go
	s.setAppliedIndex(ep.appliedi)
	s.setTerm(ep.appliedt)
```

  (tested at the pin: the test above passes). Optionally also initialize both atomics from the
  boot snapshot in `run` (`server.go:801-807`), so that `Status` does not report 0 after a restart.
- **Found**: 2026-10-26, D22 J0 (the snapshot path's design pass), checking `applySnapshot`'s effect on
  `srvAppliedInv`; confirmed by reading every reader of `getAppliedIndex` at the pin.
