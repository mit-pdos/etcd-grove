---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/raft#108 issue open: the same panic, found by fuzzing; the reporter blames MemoryStorage.Snapshot answering the empty snapshot instead of ErrSnapshotTemporarilyUnavailable
---

# raft: `MemoryStorage.Compact` without a snapshot makes the leader panic "need non-empty snapshot"

**Status**: an unstated precondition (documentation), with a reachable panic when it is not met.
`MemoryStorage.Compact` does not say that the compacted entries must be covered by a snapshot
(`CreateSnapshot` or `ApplySnapshot` at or above the compaction index), and nothing checks it. If
they are not, `Snapshot()` returns the empty snapshot with a `nil` error, and a leader that has to
catch a peer up from below the compaction boundary panics.

**Where** (raft pin `509271dac`, `etc/goose.py`):

- `storage.go:265-288` `MemoryStorage.Compact`: its documentation asks only for `compactIndex ≤
  raftLog.applied`; it moves `ents[0]` to `compactIndex` and leaves `ms.snapshot` alone.
- `storage.go:208-214` `MemoryStorage.Snapshot`: returns `ms.snapshot` (empty for a storage that
  never had `CreateSnapshot`/`ApplySnapshot`) and `nil`.
- `raft.go:618-629` `maybeSendAppend` (`term` at 625): `r.raftLog.term(pr.Next-1)` fails with `ErrCompacted`, so it
  calls `maybeSendSnapshot`; `raft.go:666-689` `maybeSendSnapshot`, line 681: `if IsEmptySnap(snapshot) {
  panic("need non-empty snapshot") }`.
- The `Storage` interface (`storage.go:86-95`) says of `FirstIndex` that "older entries have been
  incorporated into the latest Snapshot", which implies the precondition for a `Storage` in general,
  but `MemoryStorage.Compact`, the method that creates the situation, does not repeat it, and
  `Snapshot` says only "returns the most recent snapshot".

**What happens**: `issues/raft-memorystorage-compact-without-snapshot/compact_without_snapshot_test.go`
(package `raft`, at the pin and at etcd-io/raft main `638f42739`): a `MemoryStorage` with entries
1..10, `Compact(5)` with no snapshot; the node becomes leader of `{1, 2}`; peer 2 rejects the probe
with hint 0, `MaybeDecrTo` sets `Next = 1`, `term(0)` is compacted, and `maybeSendSnapshot` panics
with `need non-empty snapshot`. The test passes (it expects the panic) at both revisions.

A second way to the same panic, which may be the fuzzer's (#108 says "a leader was elected without
the snapshot being recorded to storage"): a node that restored a `MsgSnap` and called `Advance`
without `ApplySnapshot` of the `Ready`'s snapshot; its log then claims indexes its storage does not
have, `term(Next-1)` fails, and the storage's snapshot is empty. That is a violation of the `Ready`
contract (persist the snapshot before `Advance`), not of `Compact`'s.

**Expected**: either `Compact` documents (or checks, returning an error) that `compactIndex` must be at
or below the storage's snapshot index, or `maybeSendSnapshot` treats an empty snapshot like
`ErrSnapshotTemporarilyUnavailable` (log and return `false`) instead of panicking.

**How the proof handles it**: by a premise. The `Storage` contract's `Snapshot` clause
(`Proof/go_etcd_io/raft/v3/InvStorage.lean:398-410`, "a compacted storage has a snapshot", D11 of
`notes/decisions.md`) promises a non-empty snapshot once `σ.prev.index ≠ 0`, and the `MemoryStorage`
instance carries it as a pure premise, `σ.prev.index' ≠ 0 → σ.ss.index' ≠ 0`
(`Proof/go_etcd_io/raft/v3/MemstorageInstance.lean:84,249-251`). `MemoryStorage.Compact.spec`
(`Spec/go_etcd_io/raft/v3/MemoryStorage__Compact.lean`) leaves `ss` unchanged, so whoever calls
`Compact` has to re-establish the premise; in etcd that is `EtcdServer.snapshot`, which calls
`CreateSnapshot` first and is not verified. With the premise, `raftLog.snapshot.spec` returns a
non-empty snapshot and the panic is dead (`maybeSendSnapshot.spec`'s premise `prev.index ≠ 0`, from
`maybeSendAppend`'s progress bound `PrOk`).

**Possible fixes**: document the precondition on `Compact` ("`compactIndex` must not exceed the index
of the snapshot last created or applied"); or return an error from `Compact` when
`compactIndex > ms.snapshot.Metadata.Index`; or, in `maybeSendSnapshot`, log and return `false` for
an empty snapshot (the storage is then "temporarily unavailable" until the application creates one).

**Found**: 2026-10-16, triage of etcd-io/raft#108 against the D11 storage premise
(`notes/bug-triage/raft-108.md`).
