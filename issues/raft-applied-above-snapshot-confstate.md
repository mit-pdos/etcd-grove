---
upstream: unchecked
---

# raft: `Config.Applied` above the storage's snapshot skips the configuration changes in between

- **Status**: an unstated precondition (documentation). `Config.Applied` is documented as "the last
  applied index"; raft then returns no entry at or below it, and takes its configuration from
  `Storage.InitialState`'s `ConfState`. Nothing says that `ConfState` must then be the configuration
  *as of `Applied`*. A `MemoryStorage`'s `InitialState` answers its snapshot's `ConfState`, so an
  application that restarts with `Applied` above its snapshot (its state machine durable past the
  snapshot, as the documentation's "the last applied index" invites) loses every configuration
  change between the two: raft never returns those entries, so the application cannot
  `ApplyConfChange` them again. The node runs with a stale configuration: disjoint quorums, two
  leaders.
- **Where** (raft v3.7.0, the fork `upamanyus/etcd` `raft37-goose-lean-a2`, `565c2bd`, the pin of
  `etc/goose.py`): `raft.go:147-151` (`Config.Applied`'s documentation); `raft.go:444-485`
  (`newRaft`: the configuration from `InitialState`, then `raftlog.appliedTo(c.Applied)`);
  `storage.go:129-133` (`MemoryStorage.InitialState`: the snapshot's `ConfState`).
- **What happens**: `examples/kvdurable/applied_test.go`, `TestAppliedAboveConfState`: a storage
  with a snapshot at 1 (the single voter 1) and a committed entry 2 that adds voter 2, restarted with
  `Applied = 2`. Node 1 counts itself the only voter, campaigns, and becomes leader alone; entry 2
  is never returned. A second node that applied entry 2 counts `{1, 2}`: the two configurations do
  not intersect as raft assumes.
- **Expected**: either the documentation says that `InitialState`'s `ConfState` must be the
  configuration at `Applied` (the storage's snapshot at or above every configuration change up to
  `Applied`; with a `MemoryStorage`, `Applied` at most the snapshot's index unless no configuration
  change lies between), or raft reads the configuration changes in `(snapshot, Applied]` itself.
- **How the proof handles it**: the durable node API's candidate (`RestartNode`, notes/STATUS.md
  "examples/kvdurable and the durable node API") takes `Applied = 0` or `D.prev ≤ Applied ≤ the
  snapshot's index`, which is what `examples/kvdurable` does (`Cluster.start`) and what etcd does
  (it leaves `Applied` unset).
- **Possible fixes**: a sentence in `Config.Applied`'s documentation (above); or in `newRaft`, a
  check that no configuration change lies in `(firstIndex-1, Applied]` above the storage's snapshot
  (an error, as for the other `Config` checks).
- **Found**: 2026-10-31, by the `spec-reviewer` agent reviewing the durable node API's candidate
  (its `Applied` premise allowed `Applied ≤ hs.Commit`); reproduced the same day.
