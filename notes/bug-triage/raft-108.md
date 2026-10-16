# etcd-io/raft#108: memory storage loading snapshot bug

<https://github.com/etcd-io/raft/issues/108>. Open since 2023-10-20, no label, no comment, no fix.
Found by a fuzzer (a research group's "raft-fuzzing" harness, 3 nodes); the harness is not shown.

**The report.** A leader panics with `need non-empty snapshot` in `raft.maybeSendAppend` →
`maybeSendSnapshot`, reached from `stepLeader` → `bcastAppend`. The reporters' diagnosis:
`MemoryStorage.Snapshot` returns the empty snapshot instead of `ErrSnapshotTemporarilyUnavailable`
when it has none, and "the error occurred when a leader was elected without the snapshot being
recorded to storage".

## Classification

**A-pre** (reproduced at the pin), secondary **O-path** for the second candidate cause. The decisive
fact: the panic is excluded by a premise on the storage, `σ.prev.index ≠ 0 → σ.ss.index ≠ 0` (a
compacted `MemoryStorage` has a snapshot: `Proof/go_etcd_io/raft/v3/MemstorageInstance.lean:84,
249-251`, the `Snapshot` clause of the storage contract, `InvStorage.lean:398-410`, D11 of
`notes/decisions.md`). `MemoryStorage.Compact` does not state that precondition, does not check it,
and its spec leaves the snapshot unchanged, so a caller that compacts without `CreateSnapshot`
violates the premise and gets the panic. Reproduced by a Go test at the pin and at raft `main`
(`issues/raft-memorystorage-compact-without-snapshot/compact_without_snapshot_test.go`).

The harness is unknown, so the diagnosis is not settled. Two causes reach the same panic:

1. **Compaction without a snapshot** (A-pre, reproduced): `Compact(i)` on a storage whose snapshot
   index is below `i`. `term(Next-1)` fails with `ErrCompacted`, `Snapshot()` returns the empty
   snapshot and `nil`.
2. **A `Ready` snapshot not persisted** (the reporters' wording, "a leader was elected without the
   snapshot being recorded to storage"): a follower restores a `MsgSnap`, the harness calls
   `Advance` without `ApplySnapshot`; the log then claims indexes the storage lacks, and when the
   node later leads, `term(Next-1)` fails with `ErrUnavailable` and the storage's snapshot is empty.
   This breaks the `Ready` contract (persist the snapshot before `Advance`); in the proof, the
   `RawNode` level does not reach it at all: `ownRawNode` requires `s.logst.snap = none`
   (`Proof/go_etcd_io/raft/v3/InvRawnode.lean:1042`), so a received snapshot through `Ready` is
   outside the verified API (O-path; proposal `raft-pending-snapshot-ready`, as for raft#157).

## The code path and its verification state

Source: `/shared/etcd-grove-triage/coord/verified.txt` (raft pin `509271dac`).

| Go function | State | Spec |
|---|---|---|
| `stepLeader` → `bcastAppend` → `sendAppend` | verified | `Spec/go_etcd_io/raft/v3/{stepLeader,raft__bcastAppend,raft__sendAppend}.lean` |
| `raft.maybeSendAppend` | verified | `Spec/go_etcd_io/raft/v3/raft__maybeSendAppend.lean` |
| `raft.maybeSendSnapshot` | verified | `Spec/go_etcd_io/raft/v3/raft__maybeSendSnapshot.lean` (premise `prev.index ≠ 0`) |
| `raftLog.snapshot` | verified | `Spec/go_etcd_io/raft/v3/raftLog__snapshot.lean` (non-empty result) |
| `MemoryStorage.Snapshot`, `Compact`, `CreateSnapshot` | verified | `Spec/go_etcd_io/raft/v3/MemoryStorage__{Snapshot,Compact,CreateSnapshot}.lean` |
| `MemoryStorage` meets the `Storage` contract | proved under the snapshot premise | `Proof/go_etcd_io/raft/v3/MemstorageInstance.lean:84` (`is_Storage_MemoryStorage`) |
| etcd's `EtcdServer.snapshot`, `compactRaftLog` (the real callers of `CreateSnapshot`/`Compact`) | assumed (axioms) | `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__{snapshot,compactRaftLog}.lean` |

## The argument (step 4)

1. *As the spec sees it.* A leader at `s` with `PrOk` for peer 2 (`1 ≤ Next ≤ lastIndex + 1`),
   storage at `σ` with `σ.prev.index = 5`, `σ.ss.index = 0`. `maybeSendAppend` reads `term(Next-1)`
   with `Next = 1`: `ErrCompacted`. `maybeSendSnapshot.spec` (premise `uint.Z s.logst.prev.index' ≠
   0`, met) calls `raftLog.snapshot`, whose postcondition promises `sv.Metadata'.Index' ≠ W64 0`
   — obtained from `HSnapshot`'s `σ.prev.index' ≠ W64 0 → sv.Metadata'.Index' ≠ W64 0`. The real
   storage returns index `0`. So the outcome contradicts the clause — and the clause is exactly
   what the `MemoryStorage` instance does *not* prove unconditionally: it takes it as the premise
   `σ.prev.index' ≠ W64 0 → σ.ss.index' ≠ W64 0` on `ownStorage` (`memOwnStorage`).
2. *Premises against the setting.* `MemoryStorage.Compact.spec` (`Spec/go_etcd_io/raft/v3/
   MemoryStorage__Compact.lean`) returns `ownMemoryStorage ms γs (memStorCompacted σ ci t)` with
   `ss` unchanged: from `σ.ss.index = 0` and `ci = 5` the premise is false afterwards. Its doc says so
   indirectly ("`memStorMeta`, which the application keeps, is not taken, so it still holds the
   stored snapshot"); the instance's header says the premise holds "after a `CreateSnapshot`/
   `Compact` pair, which keeps `prev.index ≤ ss.index`". The fuzzer (cause 1) or the test violates
   it; so A-pre, not X. The test: `Compact(5)` on entries 1..10 with no snapshot, `becomeLeader`,
   a rejection with hint 0 from peer 2 → `panic: need non-empty snapshot`.
3. *Does etcd meet it?* Yes, by its code: `compactRaftLog(snapi)` compacts at `snapi -
   SnapshotCatchUpEntries ≤ snapi`, after `snapshot` stored `CreateSnapshot(appliedi)`
   (`server/etcdserver/server.go:2102,2150` at the etcd pin). But both are axioms here
   (`EtcdServer.compactRaftLog.spec`: pre `srvLgReader s`, post the same, no storage resource), so the
   premise is discharged for etcd by nobody.
4. *Documentation.* The `Storage` interface says older entries "have been incorporated into the
   latest Snapshot" (`storage.go:87`), which implies the premise for a `Storage` in general, but
   `MemoryStorage.Compact`, the method that creates the state, says only "not greater than
   `raftLog.applied`" (`storage.go:265-267`). That is the unstated precondition recorded in
   `issues/raft-memorystorage-compact-without-snapshot.md`.

Trust-base remark (not this bug's cause): `EtcdServer.compactRaftLog.wp_proof` and
`EtcdServer.snapshot.wp_proof` postulate triples whose frames do not mention the `MemoryStorage`
they write (`Compact`, `CreateSnapshot`). They are harmless only while no verified code holds
raft's `ownMemoryStorage` at a fixed `σ` across those calls; `raft-compact-needs-snapshot` below
would make that explicit.

## Proposal

**Slug `raft-compact-needs-snapshot`.** Raft side: give `MemoryStorage.Compact.spec` the premise
`uint.Z ci ≤ uint.Z σ.ss.index'` (and move the instance's snapshot premise into `ownMemoryStorage`
as `prev.index ≤ ss.index`, kept by `Compact`, `CreateSnapshot`, `ApplySnapshot` and `Append`), so
that `memOwnStorage` needs no external premise and the storage contract's `Snapshot` clause can be
strengthened to `prev.index ≤ Index` (which `raft-progress-match-lt-next`, raft#148, also needs).
etcd side: replace the `snapshot`/`compactRaftLog` axioms by specs that own the server's
`MemoryStorage` resource: `snapshot` returns `ss.index = appliedi`, `compactRaftLog(snapi)` requires
`snapi ≤ ss.index` (folds into `server-snapshot-ci-latest`, which already proposes proving
`EtcdServer.snapshot`). Cost: raft side small (~4 specs, one conjunct); etcd side small to medium
(two functions, 59 lines, plus threading the storage resource through the apply loop's
`snapshotIfNeededAndCompactRaftLog`). Upstream, the issue file's fixes (document `Compact`'s
precondition, or treat an empty snapshot as temporarily unavailable).

## Files

- `issues/raft-memorystorage-compact-without-snapshot.md` (new), with the reproduction
  `issues/raft-memorystorage-compact-without-snapshot/compact_without_snapshot_test.go` (passes,
  i.e. panics as described, at raft `509271dac` and at etcd-io/raft `main` `638f42739`).
