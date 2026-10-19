---
upstream: reported
checked: 2026-10-19
links:
  - etcd-io/raft#534 issue open: this bug, reported 2026-10-19
  - etcd-io/raft#83 issue open: related, not this bug: make StepDownOnRemoval the default (would avoid it)
candidate: issues/upstream/raft-readindex-removed-leader/
---

# raft: a leader that removed itself answers `ReadOnlySafe` read index requests at once, with a stale index

- **Status**: bug, reproduced by a Go test. Split off
  [raft-readindex-singleton-stale](raft-readindex-singleton-stale.md) (its execution 2, the removed leader) on
  2026-10-18, to be reported and fixed separately upstream; the fork's fix (`509271dac`) covers both.
- **Where** (etcd-io/raft `main` 638f42739): `stepLeader`, `MsgReadIndex` (`raft.go:1355-1361`): the single-voter
  shortcut answers at once with the leader's commit index when `IsSingleton()` holds; `IsSingleton`
  (`tracker/tracker.go:158-162`) only counts voters (`len(Voters[0]) == 1 && len(Voters[1]) == 0`), whoever the
  voter is; `switchToConfig` keeps a removed leader leader unless `StepDownOnRemoval` is set.
- **What happens**: nodes 1 and 2; node 2 leads, removes itself, and both apply the removal; node 2 stays leader
  with configuration `{1}`, so `IsSingleton()` holds at node 2. Node 1, the only voter, becomes leader and commits
  `y` (index 4). A read index request at node 2 is answered at once with index 2, missing `y`
  (`TestReadOnlyForRemovedLeader` on the fork branch `fix/raft-readindex-removed-leader`; fails on `main` with
  `"2" is not greater than or equal to "4"`).
- **Expected**: `ReadOnlySafe` "guarantees the linearizability of the read only request by communicating with the
  quorum" (`raft.go:61-62`); node 2 talks to nobody.
- **How the proof handles it**: see [raft-readindex-singleton-stale](raft-readindex-singleton-stale.md) (the fork
  pins the fixed raft).
- **Possible fixes**: `IsSingleton(id)`, "id on its own constitutes a quorum" (the candidate); or set
  `StepDownOnRemoval`.
- **Found**: 2026-10-14 with its sibling (review of the reconfiguration paper proof); split 2026-10-18.
