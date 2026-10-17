---
upstream: unchecked
checked: 2026-10-16
links:
  - etcd-io/raft#47 pr open: adds the check this finding asks for (appendEntry panics on an out-of-order term; restore refuses a snapshot of a later term), found by this repository's verification of that PR; does not state the precondition in Storage's documentation
  - issues/raft-commit-lost-with-entries-kept.md: related (entries persisted without their HardState), not the same field
---

# raft: a `Storage` whose `HardState.Term` is below its last entry's term makes a leader append entries of a lower term

- **Status**: undocumented precondition. raft reads `HardState` and the log from `Storage` in
  `newRaft` and checks only the commit index against them (`loadState`), not the term; the code needs the persisted term to be at least the
  last entry's (and the snapshot's) term, and the `Storage` documentation does not say so.
  etcd-io/raft#47 (open) adds a panic where it matters.
- **Where** (etcd-io/raft v3.7.0 plus the fork's fix, `raft37-goose-lean` `509271dac`, the
  revision `etc/goose.py` pins):
  - `storage.go:51-56`: `Storage.InitialState` ("returns the saved HardState and ConfState
    information"): nothing about the term relative to the entries;
  - `raft.go:439` `newRaft` / `loadState`: takes `HardState.Term` as `r.Term` as is;
  - `raft.go:812-817` `appendEntry`: stamps `r.Term` on the new entries after the last entry,
    whatever its term.
- **What happens**: a single voter restarted from a `MemoryStorage` with entries of terms 1, 2, 3
  and `HardState{Term: 1}` campaigns, wins term 2 and appends its empty entry at index 4 with term
  2: its log's terms are `[1 2 3 2]`, and the `MsgApp`s it would send to a follower carry `LogTerm: 3` with an
  entry of term 2. Every Raft argument that a log's terms do not decrease (log matching, leader
  completeness) fails from there. Reproduction: `notes/pr-verify/raft-47/raft47_probe_test.go`,
  `TestProbeRaft47InconsistentStorage` (on the pinned revision it fails with `no panic: state
  StateLeader at term 2, log terms [1 2 3 2]`; with raft#47 it passes: `appending out-of-order
  term: 2 < 3`). The same state is reached without inconsistent storage only through a message
  that no correct leader sends: a `MsgSnap` whose snapshot term is above the message's term
  (restored by `raft.restore`; raft#47 refuses it), or a `MsgApp` whose entries' terms are above
  the message's term (accepted: `handleAppendEntries` does not check them; raft#47 panics only at
  the node's next won election, `notes/pr-verify/raft-47/review47_msgapp_test.go`).
- **Expected**: either `Storage` documents that `HardState.Term` is at least the term of the last
  entry and of the snapshot (raft itself persists them that way: a `Ready`'s `HardState` carries
  the term of its entries), or raft checks it, in `newRaft` (failing at start-up) or where the
  log would go out of order (raft#47's `appendEntry` panic).
- **How the proof handles it**: outside the verified start paths: `RestartNode.spec`
  (`Spec/go_etcd_io/raft/v3/RestartNode.lean`) starts from an empty storage (`σ.ents = []`,
  `HsEmpty hs`) and `StartNode.spec` from the bootstrap log at term 1, where the ghost state's
  `TermsLe` holds (no term in a node's full log is above its own); `ownRaftPhys` alone admits a
  persisted log ahead of the persisted term (the pre-vote premise of `raft.Step.spec`). On the
  branch `pr-verify/raft-47`, `appendEntry` with raft#47 needs `LastTermLe`
  (`Spec/go_etcd_io/raft/v3/raft__appendEntry.lean`), which `Step` takes from `TermsLe`.
- **Possible fixes**: document the precondition on `Storage.InitialState`; check it in `newRaft`
  (as the reviewers of raft#47 suggested for the `appendEntry` check).
- **Found**: 2026-10-16, verifying etcd-io/raft#47 (`notes/pr-verify/raft-47.md`).
