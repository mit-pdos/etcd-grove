---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#18055 issue open: this bug (robustness test; root cause by ahrtr, "lock the snapshot file until it has been applied")
  - etcd-io/etcd#20133 issue closed: duplicate (Antithesis, main 3be967f, default configuration)
  - etcd-io/etcd#20657 issue closed: duplicate (3.5.18, two snapshots at index 17 and 18)
  - etcd-io/etcd#21082 pr closed: an earlier fix attempt, unmerged
  - etcd-io/etcd#22046 pr open: keep snapshot db files until they have been applied, with a test
---

# etcdserver: a second incoming snapshot deletes the `.snap.db` of one still being applied

- **Status**: a bug (a reachable panic: `applySnapshot` → `lg.Panic("failed to open snapshot
  backend")`; the member stops and recovers from the newer snapshot on restart).
- **Where** (etcd at the pin `107edf7e4`, `etc/goose.py`):
  - `server/etcdserver/raft.go:174-341` (`raftNode.start`): for a `Ready` with a snapshot, it
    sends the `toApply` (`:232`), saves, sends `notifyc` (`:274`), and calls
    `r.storage.Release(raftSnap)` (`:281`). After the second `notifyc` send (`:302`) it goes on to
    the next `Ready` without waiting for the apply to open its snapshot.
  - `server/etcdserver/api/snap/snapshotter.go:45-70` (`ReleaseSnapDBs`): deletes every `*.snap.db`
    with index `<` the released snapshot's, including one whose apply is in flight.
  - `server/etcdserver/server.go:1001-1050` (`applySnapshot`): receives `notifyc` (`:1037`), takes
    `s.bemu` (`:1040`), then `OpenSnapshotBackend` (`:1048`) → `DBFilePath(i)` fails, and it panics
    (`:1050`).
- **What happens**: a follower gets `MsgSnap` `i` and then `j > i` before its apply goroutine
  has opened `i.snap.db`. Processing `Ready` `j` runs `ReleaseSnapDBs(j)` and deletes
  `i.snap.db`, and `applySnapshot(i)` panics. Reproduced upstream in robustness tests and Antithesis
  (logs in #18055, #20133, #20657). The deletion step, as a unit test at the pin (`server/etcdserver/api/snap`,
  `issues/etcd-snapshot-db-released-before-apply/release_pending_test.go`; passes at the pin,
  go1.27.2, i.e. the file is gone; it does not reproduce the panic itself):

  ```go
  func TestReleaseRemovesPendingSnapDB(t *testing.T) {
  	ss := New(zaptest.NewLogger(t), t.TempDir())
  	for _, id := range []uint64{17, 18} { // two snapshots received in quick succession
  		if _, err := ss.SaveDBFrom(bytes.NewReader([]byte("db")), id); err != nil {
  			t.Fatal(err)
  		}
  	}
  	// raftNode.start, Ready with snapshot 18: storage.Release -> ReleaseSnapDBs
  	if err := ss.ReleaseSnapDBs(&raftpb.Snapshot{Metadata: &raftpb.SnapshotMetadata{Index: new(uint64(18))}}); err != nil {
  		t.Fatal(err)
  	}
  	// applySnapshot of snapshot 17: OpenSnapshotBackend -> DBFilePath(17)
  	if _, err := ss.DBFilePath(17); !errors.Is(err, ErrNoDBSnapshot) {
  		t.Fatalf("expected ErrNoDBSnapshot, got %v", err)
  	}
  }
  ```

  The interleaving needs `applySnapshot(17)` to sit between `server.go:1037` and `:1048` while the
  loop handles the next `Ready`. A gofail at `applyBeforeOpenSnapshot` (`:1047`) makes it
  deterministic, as PR #22046's test does.
- **Expected**: no panic. A snapshot handed to the apply goroutine stays on disk until it is
  opened (or superseded and skipped).
- **How the proof handles it**: the branch is dead in the proofs. `raftNode.start` and
  `applySnapshot` are verified under the `raft.Node` contract that a `Ready` carries no snapshot
  (`rnReadyData`, `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRaftNode.lean:190`; `rnApP`,
  `:682`; `EtcdServer.applySnapshot.spec` takes `ap.snapshot = nil`,
  `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applySnapshot.lean:30`). Raft's own specs
  match that scope (`MsgSnap` is not in `netStepTypes`, `Proof/go_etcd_io/raft/v3/InvRawnode.lean:465`).
  The snapshotter is names only. Triage: `notes/bug-triage/etcd-18055.md` (A-pre, proposal
  `server-apply-snapshot`: `.snap.db` files as resources, which the pin's `Release` cannot give up).
- **Possible fixes**: keep a released snapshot's file while its apply is pending, e.g. a set of
  in-use indices in `Snapshotter` that `ReleaseSnapDBs` skips, removed after `OpenSnapshotBackend`
  (#22046). Or release only below the applied snapshot index: call `Release` from the apply
  side after `applySnapshot`. Or have `applySnapshot` skip a snapshot superseded by a newer pending
  one.
- **Found**: 2026-10-16, bug triage (G17) of etcd-io/etcd#18055.
