# etcd-io/raft#157: invariants gap: committing a stale snapshot

<https://github.com/etcd-io/raft/issues/157>. Open, labeled `enhancement`, filed 2024-02-06 by
pav-kv against raft `073f90d1`. No fix, PR or commit. The code it names is unchanged at the raft
pin `509271dac` and on `raft-upstream/main` (the only later change to `log_unstable.go` is
`1c41d93f2`, which drops the shrinking in `shrinkEntriesArray`).

**The report.** It is a conjecture to investigate, not an observed failure. `unstable` keeps an
undocumented invariant: when `snapshot != nil`, `offset == snapshot.Metadata.Index + 1`, which
makes the snapshot a "wide entry" just before `entries`. `maybeTerm`, `maybeLastIndex` and the
size accounting rely on it. `unstable.truncateAndAppend`'s arm `fromIndex <= u.offset`
(`log_unstable.go:206` at the pin) replaces the entries and sets `offset = fromIndex` but leaves
`u.snapshot` alone. So a batch starting *below* the offset would leave
`offset < snapshot.index + 1`, and the snapshot's index could exceed `lastIndex()`. The question
is whether a caller can submit such a batch. The one comment (MrDXY, 2024-03-18) says yes: a stale
`MsgApp` (prev index 0, entries 1..2) arrives at a follower after it restored a snapshot at
index 2, and is appended below the snapshot.

## Classification

**N**: not a bug. The conjectured state cannot be reached, and the proof shows it. Secondary
**O-fn**: one path is outside the verified scope (below).

The decisive fact: the issue's invariant is a conjunct of `ownRaftLog`, which every verified
raft method preserves. With a pending snapshot `sid`, `LogStoreOk` (`InvRaftlog.lean:393-398`)
gives `prev = sid` and `sents = []`, and `%Hoffset` (`InvRaftlog.lean:530-531`) gives
`unstable.offset = prev.index + |sents| + 1 = sid.index + 1`. The proof also preserves it at
`truncateAndAppend`'s only caller, `raftLog.append`, whose premise
`committed < ents[0].Index` (`Spec/go_etcd_io/raft/v3/raftLog__append.lean:73`, the code's
`Panicf` at `log.go:137`) combines with `%Happlied`'s `prev.index ≤ committed`
(`InvRaftlog.lean:534`) to give `fromIndex ≥ sid.index + 1 = offset`. So the
`fromIndex < offset` case never runs while a snapshot is pending. The `==` case leaves the offset
unchanged.

The comment's scenario is wrong. `raft.restore` sets `committed = 2`, so the stale `MsgApp` hits
`handleAppendEntries`'s first test, `a.prev.index (0) < committed (2)` (`raft.go:1788`). The
follower answers with its commit index and appends nothing. The verified proof takes this branch
(`Proof/go_etcd_io/raft/v3/raft__handleAppendEntries.lean:120-130`, "stale: acknowledge
`committed`").

## The code path and its verification state

Source: the proof files directly, because `verified.txt` was not yet written. Each function below
has a `theorem … wp_proof` with no `sorry` and is listed in `etc/link-lean-first-raft.txt`, so it
is linked in `Proof/go_etcd_io/raft/v3/Link.lean` (for example `unstable.wp_truncateAndAppend`,
Link.lean:1015). The axioms were not traced (`.lake/tcb.json` is absent). None of the step-4
argument depends on a trust-boundary axiom.

| Go function | State | Spec |
|---|---|---|
| `unstable.truncateAndAppend` | verified, all three arms | `Spec/go_etcd_io/raft/v3/unstable__truncateAndAppend.lean` (snapshot unchanged, `offset := min(fromIndex, offset)`) |
| `raftLog.append` | verified | `Spec/go_etcd_io/raft/v3/raftLog__append.lean` (premise `committed < e0.Index`) |
| `raftLog.maybeAppend` | verified | `Spec/go_etcd_io/raft/v3/raftLog__maybeAppend.lean` (premise: a conflict lies above `committed`) |
| `raft.handleAppendEntries`, `stepFollower`, `stepCandidate`, `raft.Step` | verified | `Spec/go_etcd_io/raft/v3/raft__handleAppendEntries.lean`, `raft__Step.lean`. `raft.Step` discharges the conflict premise from the protocol (`Proof/go_etcd_io/raft/v3/raft__Step/MsgApp_gt.lean:60`) |
| `raft.handleSnapshot`, `raft.restore`, `raftLog.restore`, `unstable.restore` | verified | their `Spec/go_etcd_io/raft/v3/` files (they set `committed = sid.index`) |
| `unstable.stableTo`, `raftLog.stableTo` | verified | `raftLog__stableTo.lean`, premise `StableOk` (`Proof/go_etcd_io/raft/v3/InvReadylog.lean:115`) |
| `raftLog.stableSnapTo`, `unstable.stableSnapTo`, `raft.appliedSnap`, `MsgStorageAppendResp`'s snapshot arm | not verified (out of scope, `notes/STATUS.md` "Snapshots at the public API (stage S)", item 3) | none |

## The argument (step 4)

1. **The behavior, as the spec sees it.** A state `ls` with `ls.snap = some sid`, then a
   `raft.Step` that reaches `raftLog.append` with `e0.Index < sid.index + 1`, which leaves
   `offset < sid.index + 1` with the snapshot still pending.
2. **Premises.** `raft.Step`'s precondition allows any `s.logst`, including a pending snapshot
   (only `MsgStorageAppendResp` must carry `sn = none`, `raft__Step.lean:380`). So stepping a
   `MsgApp` under a pending snapshot is in scope. Neither the issue nor the comment violates a
   premise.
3. **Axioms and model.** Nothing involved (no storage reads, no time).
4. **The postcondition excludes it.** `raftLog.append` returns `ownRaftLog l (logTruncateAppend
   ls ents)` with `snap` unchanged, so its `LogStoreOk`/`%Hoffset` again force
   `offset = sid.index + 1`. The premise that makes this provable is `committed < e0.Index`.
   `handleAppendEntries` establishes it before `maybeAppend` through the stale test
   (`a.prev.index ≥ committed`), and `maybeAppend` through its conflict premise. A follower
   therefore never appends below a pending snapshot. This is the issue's "best case", proved.
   The other ways to move `offset` are also covered. `unstable.stableTo` can move it above
   `sid.index + 1`, but `StableOk` requires `ls.snap = none` whenever it hits
   (`InvReadylog.lean:115-119`). `restore` sets it to the new snapshot's index plus 1.

   The issue is right that the invariant is load-bearing. The proof uses it for `term`,
   `firstIndex`/`lastIndex` and `slice` (the `LogStoreOk` doc comment, `InvRaftlog.lean:377-392`).

**The gap the proof does not cover (secondary, O-fn).** The real code breaks the invariant briefly
in one place: a `MsgStorageAppendResp` that carries both an entry index and the snapshot
(`raft.go:1197-1203`). `stableTo` runs first and may move `offset` past `sid.index + 1` while the
snapshot is still set. `appliedSnap` → `stableSnapTo` then clears the snapshot if its index still
matches. If a newer snapshot was restored in between, the `stableTo` misses: `restore` emptied
`entries`, and an entry with the acknowledged term at that index would contradict Log Matching
with the restore's term mismatch. By that argument (not proved) nothing reads the broken state.
This path, and with it a pending snapshot at the `RawNode` level (`ownRawNode` requires
`s.logst.snap = none`, `InvRawnode.lean:1042`), is outside the verified scope. The end-to-end
results therefore cover a pending snapshot only within single `raft.Step`s.

## Proposal (step 6)

**Slug `raft-pending-snapshot-ready`** (stage S, items 2–3 of `notes/STATUS.md`, "Snapshots at the
public API (stage S)"). The goal is to verify `raftLog.stableSnapTo`/`unstable.stableSnapTo`,
`raft.appliedSnap` and `MsgStorageAppendResp`'s snapshot arm, and to drop `ownRawNode`'s
`s.logst.snap = none`. Statement sketch: `raft.Step`'s
`MsgStorageAppendResp` premise becomes `sn = some sv → snapId sv = sid ∧ StableOk' ls id` (where
`StableOk'` allows a hit when the snapshot it acknowledges is `ls.snap`), and the postcondition
is `ownRaftLog l (logStableSnapTo (logStableTo ls id) sid)`. The existing `ownRaftLog` (with
`%Hoffset`) must hold again at return, though not between the two calls. Cost: about 4 small
functions in raft plus the `RawNode` design work STATUS lists (19 files read `Hsnap`;
`Ready`/`Advance` with `snapshotInProgress`; the application's snapshot obligations). It is
moderate to large and mostly design work, not proof volume. It would not catch a bug here,
because none is known. It would turn the transient-violation argument above into a proved
statement.

A cheap documentation option, upstream and not ours: the invariant and the premise that keeps it
(`committed < fromIndex`, hence `fromIndex ≥ offset` under a pending snapshot) can be stated at
`truncateAndAppend`, which is what the issue asks for. The spec above is that documentation.

## Findings (step 7)

None. The bug does not exist at the pin, so there is no `issues/` file. The specs and proofs show
no problem, so there is no `notes/` entry.
