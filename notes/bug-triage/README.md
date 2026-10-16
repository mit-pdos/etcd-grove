# Bug triage against the proofs

Upstream bug reports classified against this repository's proved specs, per
`.claude/skills/bug-triage/SKILL.md`: how could the bug happen despite the proofs, and what
verification would exclude its class. One report per bug, `<repo>-<n>.md`.

## Batch 2026-10-16 (five correctness reports from each of etcd-io/etcd and etcd-io/raft)

The pins: etcd `107edf7e4`, raft `509271dac` (`etc/goose.py`). The per-function verification
states were read from the `Spec/`, `Proof/` and `Link.lean` files (the inventory
`etc/verified-code.py` needs an up-to-date build, which was not there when the batch ran).

| Bug | Title | Class | Decisive fact | Proposal |
|---|---|---|---|---|
| [etcd#21536](etcd-21536.md) | cache: `Get(WithRev(rev))` can return the wrong value | **F+** | fix in the pin; `store.getSnapshot.spec` pins the result to the greatest snapshot ≤ `rev`, which the buggy `AscendGreaterOrEqual` breaks on the issue's own example | (`cache-get-state-at-requested-rev`, optional) |
| [etcd#18667](etcd-18667.md) | revision in a txn's range may cause inconsistency | F− (C) | fix in the pin; `backendStep`'s txn case does not tie rejection to `checkTxn`, and non-plain txns are excluded by `txnPlain`, so proposer and followers could diverge under the spec | `txn-exact-check` |
| [etcd#19487](etcd-19487.md) | watch response revision below the starting revision | F− (O-fn) | fix in the pin; only the unspecified `watchableStore.Restore` creates the future `minRev` the bug needs (the invariant assumes `restore = false`) | `verify-watchable-restore` |
| [etcd#16666](etcd-16666.md) | wait-cluster-ready timeout gives stale linearizable reads | F− (A-model, O-pkg) | fix in the pin; the stale read needs a crash losing `HardState.Commit`, and crashes are not modeled (`embed` not translated) | `crash-restart-model` |
| [etcd#18089](etcd-18089.md) | watch drops an event when compacting on delete | F− (C-scope) | fix in the pin; the watch specs assume `crevFrozen` (no compaction), and the compaction specs mirror the code's `keepAt` | `watch-under-compaction` |
| [raft#392](raft-392.md) | with retries, read index can be stale | F (etcd half F+, raft half F−, A-pre) | both fixes in the pins; etcd's resend breaks the read loop's `rdFresh` token (F+), but raft's specs assume `rdFresh` too, stricter than v3.7's documented `ReadIndex` contract | `readindex-ctx-reuse` |
| [raft#197](raft-197.md) | follower panics on a commit-index regression | A-model (N) | the follower lost its persisted log and rejoined under its ID; `RestartNode`'s `rnInit` and the in-memory justification of acks cannot represent it; raft documents persist-before-send | `raft-durable-acks` → `crash-restart-model` |
| [raft#157](raft-157.md) | invariants gap: committing a stale snapshot | N (O-fn) | the issue's invariant is a conjunct of `ownRaftLog`; the stale `MsgApp` is rejected; only `stableSnapTo`/`appliedSnap` (unverified) break it transiently | `raft-pending-snapshot-ready` |
| [raft#354](raft-354.md) | ConfChange silently converted to a no-op | N (C-err) | documented (`node.go:141-145`), and `stepLeader`'s spec states exactly the reported outcome | `confchange-propose-outcome` |
| [raft#372](raft-372.md) | `EnterJoint` without quorum overlap | N | closed invalid; the test applied an uncommitted LeaveJoint; overlap of adjacent configurations is proved (`enterJointM_overlap`, `leaveJointM_overlap`) | — |

**Counts.** F+ 1, F (split) 1, F− 4, A-model 1, N 3; O, C and X as primary classes 0. No
soundness alert (X), and no bug found in this repository's specs. No bug of the batch is present
at the pins, so no new `issues/` file; `issues/raft-readindex-singleton-stale.md` gained related
links (etcd#16666, raft#105).

**The specs that would have excluded the bug (F+):** etcd#21536 (`store.getSnapshot.spec`), and the
etcd half of raft#392 (`Read.requestCurrentIndex`'s use of `rdFresh`).

**What lets bugs through.** Of the six F reports, five are F− at least in part: the bug is fixed in
the pinned code, but the proof as it stands would also have gone through on the buggy code. The
reasons are scope choices already recorded in `notes/STATUS.md` — no compaction under watch
(`crevFrozen`), plain transactions only (`txnPlain`), no restore of a watchable store, no crashes,
fresh read contexts — rather than wrong specs. Each is a place where a bug fixed upstream could
come back unnoticed.

## Proposals, ranked by the bugs they would have caught

| Proposal | Bugs | What | Cost |
|---|---|---|---|
| `crash-restart-model` | etcd#16666, raft#197 | a WAL contract separating persisted from unpersisted state, a restart step through `RestartNode` and the WAL bootstrap, ghost commit carried across the crash; read-notify linearizable after a restart | large; needs crash semantics Perennial's Lean port lacks (a separate Perennial proposal). The first step, `raft-durable-acks` (acks and votes justified by `ownStorage` instead of the in-memory log), is medium and needs no crashes |
| `watch-under-compaction` | etcd#18089 | drop `crevFrozen` from `syncWatchers`/`rangeEvents`; pure lemma `keepAt_main_eq` (a revision with main `c` survives compaction at `c`), already named in STATUS "Traps for 6b" | medium to large (mvcc unit 6b) |
| `txn-exact-check` | etcd#18667 | a pure `checkTxnOk`; `backendStep` rejects a txn iff `¬ checkTxnOk`; `txnPlain` widened to gets at any revision | medium; ~15 consumers of T2 re-run |
| `verify-watchable-restore` | etcd#19487 | specify `watchableStore.Restore` and `store.Restore`'s snapshot case; invariant keeps `lo ≤ minRev` for restored unsynced watchers | large (the store's log model needs a jump to a snapshot) |
| `readindex-ctx-reuse` | raft#392 (raft half) | drop `rdFresh` from raft's read-index specs; a reused context's deposit returns the existing record | small to medium, ghost layer only |
| `raft-pending-snapshot-ready` | (raft#157: no bug, closes the informal part) | verify `stableSnapTo`, `appliedSnap`, the snapshot case of `MsgStorageAppendResp`; drop `ownRawNode`'s `snap = none` | moderate to large (STATUS stage S items 2–3) |
| `confchange-propose-outcome` | (raft#354: documented behavior) | carry `stepLeader`'s accept/refuse outcome to the `RawNode`/`node` specs, enabling a spec of etcd's `configure` | small to medium |
| `cache-get-state-at-requested-rev` | (etcd#21536: already F+) | `cacheGetOk` gives etcd's state at the requested revision, not only at the snapshot's | moderate, a few hundred lines |

Side notes from the batch: the header of `Protocol/ResultsDyn.lean` says "not yet reached from Go",
out of date since stage B7 (raft#372's report); raft's `rdFresh` premise is stronger than raft
v3.7's documented `ReadIndex` contract (raft#392's report).
