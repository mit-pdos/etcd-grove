---
upstream: unchecked
checked: 2026-10-18
links:
---

# etcdserver: the apply loop compacts raft's `MemoryStorage` past `raftLog.applied`, so a campaign in that window panics in raft

- **Status**: a bug (a reachable panic), from an unmet documented precondition: raft's
  `MemoryStorage.Compact` says "It is the application's responsibility to not attempt to
  compact an index greater than raftLog.applied", and etcd's apply loop compacts above it for
  a short window. Reproduced on raft by a Go test (below), the etcd interleaving by reading
  the code; not run on etcd.
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
- **Expected**: the application keeps `Compact`'s documented bound, `compactIndex <=
  raftLog.applied`, at every moment raft may read the storage.
- **How the proof handles it**: not yet. `EtcdServer.compactRaftLog`'s and
  `EtcdServer.snapshot`'s trust-boundary specs are false (`notes/audit.md`, audit B2); their
  restatement (D19i part 1, option (A), `notes/decisions.md`) needs the bound raft publishes
  to be `raftLog.applied`, which this window breaks, so it stopped for a decision
  (`notes/STATUS.md`, "D19i part 1: stopped").
- **Possible fixes** (etcd):
  1. snapshot and compact only after raft's `Advance` of the batch: `raftNode.start` closes
     `raftAdvancedC` after every `Advance` (today it sends on it only for a batch with a conf
     change, `raft.go:333-336`, for `configure`'s waiter, which a close serves as well), and
     `applyAll` waits for it before `snapshotIfNeededAndCompactRaftLog`;
  2. or bound the compaction by the applied index before the batch (raft had applied it
     before it handed the batch out): `compacti = min(compacti, appliedi before applyEntries)`.
  The snapshot itself at `ep.appliedi` is harmless to raft (it is of a committed prefix).
- **Found**: 2026-10-18, designing D19i part 1 (which bound raft must publish for the
  application's compaction: `hasUnappliedConfChanges` reads from `applied + 1`, not from
  `applying + 1`).
