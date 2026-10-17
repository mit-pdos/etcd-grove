---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#22528 issue open: this bug (a new member joining an idle cluster stuck at "too many requests")
  - etcd-io/etcd#22516 issue open: the same bug (the member stays unpublished)
  - etcd-io/etcd#22529 pr open: the fix in applySnapshot (verified, notes/pr-verify/etcd-22529.md)
  - etcd-io/etcd#22510 pr open: the same two-line fix in applySnapshot, with its own test
  - etcd-io/etcd#22527 pr open: related, not this bug (publishV3 retries a rejected publish without waiting)
---

# etcdserver: applying a leader snapshot advances the apply loop's index but not `s.appliedIndex`

**Status**: a bug (a liveness failure: a member rejects every proposal of its own until another
member's write is applied), known upstream and fixed by two open PRs. Recorded here because the
pinned code has it and the verified model excludes it.

**Where** (fork `goose-lean` at `09669450f`, the pin of `etc/goose.py`):
`server/etcdserver/server.go:1140-1144` (`applySnapshot` sets `ep.appliedi`/`ep.appliedt` from
the snapshot; `s.appliedIndex`/`s.term` are written only by `apply`, `server.go:1923-1932`);
`server/etcdserver/raft.go:344` (`updateCommittedIndex` raises `s.committedIndex` to the
snapshot's index); `server/etcdserver/util.go:60` (`exceedsRequestLimit`, used by
`processInternalRaftRequestOnce`, `v3_server.go:1060`).

**What happens**: a member that catches up by a leader snapshot more than
`maxGapBetweenApplyAndCommitIndex` (5000) entries ahead of its `s.appliedIndex` (a new member: 0),
with no entry committed after the snapshot (an idle cluster), has `committedIndex = snapIndex`
and `appliedIndex` unchanged: every proposal it makes, its own `publishV3` included, fails with
`ErrTooManyRequests` before reaching raft, so it never publishes itself, until a write through
another member is applied. `Status` reports the stale `RaftAppliedIndex`/`RaftTerm` meanwhile.
Linearizable reads are not affected (they wait on `applyWait`, triggered with `ep.appliedi`).
Reproduction: the PR's test `TestApplySnapshotAdvancesAppliedIndexAndTerm`, which fails on the
pinned code (`notes/pr-verify/etcd-22529/`, `base.log`).

A milder form on restart: `run()` initializes `ep.appliedi`/`ep.appliedt` from the raft storage's
snapshot (`server.go:802-808`) but leaves `s.appliedIndex`/`s.term` at 0 until the first entry
after it is applied; the first `Ready`'s committed entries raise `s.committedIndex` before they
are applied, so in that window proposals are rejected and `Status` reports 0. Transient (the
first applied entry repairs it); neither PR changes it.

**Expected**: `s.appliedIndex` is the index the apply loop has applied (`AppliedIndex()`'s
documentation in `server.go`, and `exceedsRequestLimit`'s use of it).

**How the proof handles it**: the verified apply loop runs under raft's contract as modelled that
a `toApply` carries no snapshot (`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applySnapshot.lean`,
`taSnapshotAddr ap ↦□ null`), and the modelled start is a new cluster's (`InvStart.lean`,
`isServerBuilt`: the atomic and the apply thread's ghost half at the same `ai₀`, met by `NewServer`
only for `ai₀ = 0`). The apply thread's invariant pairs `ep.appliedi` with its half of the applied
index (`srvApplyRes`, `InvApplyAll.lean`), which the old code would break.

**Possible fixes**: `s.setAppliedIndex(ep.appliedi); s.setTerm(ep.appliedt)` after `applySnapshot`
sets them (etcd-io/etcd#22529, #22510); the same after `run()` initializes `ep` for the restart case.

**Found**: 2026-10-17, verifying etcd-io/etcd#22529 (`.claude/skills/etcd-pr-verify`); the restart
case by the reviewer of that verification.
