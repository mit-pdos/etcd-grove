---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#9079 issue closed: the same panic ("unexpected error getting unapplied entries (requested index is unavailable due to compaction)", etcd 3.1.9, from tickElection), but after raft restored a leader snapshot (an unstable snapshot above applied), not etcd's compaction; closed as stale; raft v3.7.0's promotable() now refuses to campaign while a snapshot is pending (checked by a raft test, 2026-10-18)
  - etcd-io/etcd#12134 pr merged: made MsgTimeoutNow go through the unapplied conf-change scan before campaigning (the scan that panics here); related, not this bug
  - etcd-io/etcd#7470 issue closed: compaction racing an incoming snapshot (ErrCompacted after two MsgSnaps); related, different path
  - etcd-io/etcd#18825 pr merged: in-memory snapshots every 100 entries (6cebf973a, v3.6.0), which make the restart trigger below reachable with default settings
  - etcd-io/etcd#17098 issue closed: proposes compacting the raft log after every apply (#18459 pr closed, unmerged); related, would widen this window to every batch
candidate: issues/upstream/etcd-compact-past-raft-applied/
---

# etcdserver: the apply loop compacts raft's `MemoryStorage` past `raftLog.applied`, so a campaign in that window panics in raft

- **Status**: a bug (a reachable panic), from an unmet documented precondition: raft's
  `MemoryStorage.Compact` says "It is the application's responsibility to not attempt to
  compact an index greater than raftLog.applied", and etcd's apply loop compacts above it for
  a short window. Reproduced on raft by a Go test, and end to end on etcd by an integration
  test (a member panics on a leader transfer right after its restart; below).
- **Where** (etcd: the fork `upamanyus/etcd`, branch `goose-lean`, at the pin of
  `etc/goose.py`; raft: `go.etcd.io/raft/v3` v3.7.0, the fork's `raft37-goose-lean`):
  - etcd `server/etcdserver/raft.go:219-336` (`raftNode.start`): for each `Ready` it hands
    the committed entries to the apply loop (`r.applyc <- ap`, 232), saves and appends the
    entries (`r.raftStorage.Append`, 287), signals `notifyc` (302 or 327) and only then calls
    `r.Advance()` (331).
  - etcd `server/etcdserver/server.go:978-999` (`applyAll`): applies the batch, waits for
    `notifyc` (989), then `snapshotIfNeededAndCompactRaftLog` (991; 1210-1219):
    `CreateSnapshot(ep.appliedi, ...)` (2102) and `compactRaftLog(ep.appliedi)` (2132-2163),
    which compacts at `appliedi - SnapshotCatchUpEntries` (or `1` while `appliedi` is at most
    `SnapshotCatchUpEntries`).
  - raft `rawnode.go:400` (`acceptReady`) moves only `raftLog.applying` when a `Ready` hands out
    committed entries; `raftLog.applied` moves when the application calls `Advance` (the
    `MsgStorageApplyResp` queued in `stepsOnAdvance`, `raft.go:1205`, `appliedTo` 737).
  - raft `raft.go:995-1021` (`hasUnappliedConfChanges`, called by `hup`, 973-983, on an election
    timeout, `Campaign` or a `MsgTimeoutNow`): scans `[applied+1, committed+1)`, and
    `Panicf`s on any error but `errBreak`; `log.go:551-565` (`mustCheckOutOfBounds`) answers
    `ErrCompacted` when `applied + 1 < firstIndex()`.
  - raft `storage.go:265-267` (`Compact`'s documentation, quoted above).
- **What happens**: between `notifyc` and `Advance`, `raftLog.applied` is still the index
  before the batch, while `ep.appliedi` is the batch's last index. If the batch held more than
  `SnapshotCatchUpEntries` committed entries (5000 by default, configurable with
  `--snapshot-catchup-entries`; a `Ready` carries up to `MaxCommittedSizePerReady` = 1 MiB of
  them, which is more than 5000 small entries; e.g. the first `Ready` after a restart replays
  up to `SnapshotCount` = 10000 entries from the WAL), or `raftLog.applied` is 0 and the batch
  makes the first memory snapshot (`compacti = 1`), the apply loop compacts above
  `raftLog.applied`. If `node.run` then processes a `MsgHup` before the `Advance` (a tick
  buffered in `tickc`, or a `MsgTimeoutNow` from the leader, both received while `node.run`
  waits for `advancec`), `hasUnappliedConfChanges` scans from `applied + 1`, below the new
  first index, gets `ErrCompacted` and panics: "error scanning unapplied entries [lo, hi):
  requested index is unavailable due to compaction".

  Reproduction on raft (the application's steps in the order etcd can take them; add to the
  raft package as `compact_past_applied_test.go`):

  ```go
  func TestCompactPastAppliedThenCampaign(t *testing.T) {
  	s := newTestMemoryStorage(withPeers(1, 2, 3))
  	rn := newTestRawNode(1, 10, 1, s)
  	var ents []*pb.Entry
  	for i := uint64(1); i <= 10; i++ {
  		ents = append(ents, &pb.Entry{Index: new(i), Term: new(uint64(1)), Data: []byte("x")})
  	}
  	// the leader 2 sends entries 1..10, committed up to 10
  	if err := rn.Step(&pb.Message{From: new(uint64(2)), To: new(uint64(1)), Type: pb.MsgApp.Enum(),
  		Term: new(uint64(1)), LogTerm: new(uint64(0)), Index: new(uint64(0)), Commit: new(uint64(10)),
  		Entries: ents}); err != nil {
  		t.Fatal(err)
  	}
  	rd := rn.Ready() // hands out 1..10 to apply; raftLog.applied stays 0
  	if err := s.Append(rd.Entries); err != nil {
  		t.Fatal(err)
  	}
  	// the apply loop, having applied 1..10, snapshots and compacts
  	if _, err := s.CreateSnapshot(10, &pb.ConfState{Voters: []uint64{1, 2, 3}}, nil); err != nil {
  		t.Fatal(err)
  	}
  	if err := s.Compact(5); err != nil { // 5 > raftLog.applied = 0
  		t.Fatal(err)
  	}
  	_ = rn.Campaign() // before Advance: panics
  }
  ```

  Run at v3.7.0 (2026-10-18): `panic: error scanning unapplied entries [1, 11): requested index
  is unavailable due to compaction`. After `rn.Advance(rd)` the same `Campaign` does not panic.

  Reproduction on etcd (2026-10-18; upstream `main` 22cc5d9ac, and the fork's `goose-lean`
  09669450f, whose `raft.go`/`server.go` differ from `main` only in `processMessages`; raft
  v3.7.0; default `SnapshotCount` and `SnapshotCatchUpEntries`): an integration test,
  `TestCompactBeforeAdvanceThenLeaderTransfer`, and a gofail failpoint in
  `etcd-compact-past-raft-applied/repro.patch`. The trigger needs no special configuration: a
  restart. A 3-member cluster takes 150 puts; a follower `F` is stopped and restarted. `F`
  has no disk snapshot (fewer than `SnapshotCount` entries), so raft restarts with
  `applied = 0` and its first `Ready` replays all 158 committed entries; the apply loop
  applies them, `appliedi = 158 > memorySnapshotIndex + 100`, so it snapshots in memory and
  compacts at `1` (`158 <= SnapshotCatchUpEntries`), above `applied = 0`. The failpoint
  `raftBeforeAdvanceOnMember` (a 5 s sleep before `r.Advance()`, on `F` only) widens the
  window; one second in, the test calls `MoveLeader(leader -> F)`. The leader still has `F`'s
  match from before the restart, so it sends `MsgTimeoutNow` at once; `F`'s `node.run`
  receives it while waiting for `advancec`, and `hup` panics:

  ```
  INFO m0.raft ... sends MsgTimeoutNow to 660efaef670f173 immediately as 660efaef670f173 already has up-to-date log
  INFO m1.raft 660efaef670f173 [term 2] received MsgTimeoutNow from 50809f9c04a15871 and starts an election to get leadership.
  panic: error scanning unapplied entries [1, 159): requested index is unavailable due to compaction
  go.etcd.io/raft/v3.(*raft).hasUnappliedConfChanges   raft.go:1018
  go.etcd.io/raft/v3.(*raft).hup                       raft.go:983
  go.etcd.io/raft/v3.stepFollower                      raft.go:1763
  go.etcd.io/raft/v3.(*node).run                       node.go:399
  FAIL	go.etcd.io/etcd/tests/v3/integration	1.306s
  ```

  Deterministic: it panicked in all 4 runs (3 on `main`, 1 on the fork). The failpoint only
  widens the window between `notifyc` and `Advance`. Without it, the campaign (here a
  `MsgTimeoutNow`) has to arrive inside that short window; that was not measured. To run (gofail v0.2.0, as
  `tests/robustness/Makefile`'s `gofail-enable`, for `server/etcdserver/` only):

  ```
  git apply issues/etcd-compact-past-raft-applied/repro.patch   # in an etcd checkout at 22cc5d9ac
  go install go.etcd.io/gofail@v0.2.0 && gofail enable server/etcdserver/
  (cd server && go get go.etcd.io/gofail@v0.2.0); (cd tests && go get go.etcd.io/gofail@v0.2.0)
  cd tests && go test ./integration/ -run TestCompactBeforeAdvanceThenLeaderTransfer -count=1 -v
  ```

  With `etcd-compact-past-raft-applied/fix.patch` (fix 1 below) applied on top, the test
  passes (5 runs: 4 on `main`, 1 on the fork). `F` now compacts only after `Advance`; on the
  `MsgTimeoutNow`, raft scans `[1, 159)`, finds the bootstrap conf changes unapplied, and
  refuses to campaign ("cannot campaign at term 2 since there are still pending configuration
  changes to apply"). The single transfer attempt then times out (the test accepts this), and
  afterwards `F` serves a put. With the fix, `go test ./etcdserver/` (server) and the
  integration tests `TestMember|TestCluster|TestV3MoveLeader|TestRestart|TestSnapshot|TestTransferLeader`
  pass.
- **Expected**: the application keeps `Compact`'s documented bound, `compactIndex <=
  raftLog.applied`, at every moment raft may read the storage.
- **How the proof handles it** (2026-10-18, D19i part 1, (A1)): the fork carries fix 1
  (`upamanyus/etcd` `goose-lean` `06aa6e6e`, pushed), re-translated; the proof follows it.
  Raft publishes a floor the application may compact and snapshot up to (`StorState.fl`,
  `isStorageWith`'s floor law): `node.go`'s `run` raises it to `applying` at the `advancec`
  rendezvous (`advInv`, `InvNode.lean`), since `node.Advance` returns there, before
  `rn.Advance` moves `applied`; in between `run` only calls `rn.Advance`, which reads nothing at
  or below the floor, and raft's reads from `applied + 1` (`hasUnappliedConfChanges`) take
  `fl <= applied` as a premise outside that window (`RNState.flw`). `node.Advance` hands the
  floor's witness to `raftNode.start`, which closes `raftAdvancedC` with it; `applyAll` takes it
  there, and `EtcdServer.snapshot` and `EtcdServer.compactRaftLog` are restated under it
  (`notes/audit.md`). Without the fix the witness would not exist when `applyAll` snapshots.
- **Possible fixes** (etcd):
  1. snapshot and compact only after raft's `Advance` of the batch: `raftNode.start` closes
     `raftAdvancedC` after every `Advance` (today it sends on it only for a batch with a conf
     change, `raft.go:333-336`, for `configure`'s waiter, which a close serves as well), and
     `applyAll` waits for it (or `s.stopping`) before `snapshotIfNeededAndCompactRaftLog`;
     `etcd-compact-past-raft-applied/fix.patch`, which makes the reproduction above pass;
  2. or bound the compaction by the applied index before the batch (raft had applied it
     before it handed the batch out): `compacti = min(compacti, appliedi before applyEntries)`.
  The snapshot itself at `ep.appliedi` is harmless to raft (it is of a committed prefix).
  The upstream candidate (2026-10-21, `issues/upstream/etcd-compact-past-raft-applied/`, branch
  `fix/etcd-compact-past-raft-applied`, rebuilt 2026-10-23 off `main` 3aaab3479) is fix 1, with a test that needs no new failpoint
  (`raftBeforeFollowerSend` with `sleep("2s")`); its `meta.md` compares the layers (raft's scan, the compact bound,
  reordering `Advance`). A restart clears the crash (checked 2026-10-23: the panicked member's data directory
  restarts with every applied entry, then campaigns without panicking), but reopens the window on each restart
  with no disk snapshot (code reading); the candidate's `meta.md`, "Impact".
- **Found**: 2026-10-18, designing D19i part 1 (which bound raft must publish for the
  application's compaction: `hasUnappliedConfChanges` reads from `applied + 1`, not from
  `applying + 1`). Reproduced end to end on etcd the same day (integration test above). The
  restart trigger (`applied = 0` at the first memory snapshot) needs the in-memory snapshots
  of v3.6.0 (etcd-io/etcd#18825); not run on v3.5.
