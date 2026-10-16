# etcd-io/raft#148: probe from an index less than match

<https://github.com/etcd-io/raft/issues/148>. Filed 2024-01-31, closed 2024-02-06; labels `bug`,
`good first issue`. Fixed by etcd-io/raft#149 (merge `073f90d1f`, commit `64394821e`, "raft: next
index shall be larger than match index").

**The report.** In `StateProbe`, `Progress.MaybeDecrTo(rejected, matchHint)` (`tracker/progress.go`)
set `pr.Next = max(min(rejected, matchHint+1), 1)`. Its staleness check is `pr.Next-1 != rejected`,
which assumes one probe in flight; a delayed rejection that happens to name the current `Next-1`
(for instance after the peer went back to `StateProbe`) with a small `matchHint` drives `Next` to or
below `Match`. The leader then re-sends entries the follower already acknowledged. The maintainer
(pav-kv): the invariant is `Next > Match`; probe/replicate are heuristics and do not affect safety,
since the follower gates every `MsgApp` against its log.

## Classification

**F−** (fixed before the pin), gap **C-perf** (secondary C-other). The decisive facts: the fix is in
the raft pin (`git merge-base --is-ancestor 073f90d1f 509271dac`: yes), and the existing specs would
have admitted the buggy line. `MaybeDecrTo`'s spec states the body verbatim, and the leader's
progress invariant `PrOk` bounds `Next` and `Match` only against the log, not against each other,
so the pre-fix `max(..., 1)` keeps every invariant. The resulting behavior (re-sending matched
entries) is safe, and the protocol model allows it: `AppOk` constrains a `MsgApp` by the leader's
log, not by the peer's `Match`.

## The code path and its verification state

Source: `/shared/etcd-grove-triage/coord/verified.txt` (raft pin `509271dac`).

| Go function | State | Spec |
|---|---|---|
| `tracker.Progress.MaybeDecrTo` | verified | `Spec/go_etcd_io/raft/v3/tracker/Progress__MaybeDecrTo.lean` (model `progressMaybeDecrTo`, `Proof/go_etcd_io/raft/v3/Defs.lean:566`) |
| `stepLeader`, `MsgAppResp` rejected | verified | `Spec/go_etcd_io/raft/v3/stepLeader.lean`; `leader_appresp_step`, `Proof/go_etcd_io/raft/v3/raft__Step/resp_lemmas.lean:253` |
| `raft.maybeSendAppend` | verified | `Spec/go_etcd_io/raft/v3/raft__maybeSendAppend.lean` |

## The counterfactual (step 5)

The buggy line, in the model: `nx := w64Max (w64Min rejected (matchHint + 1)) (W64 1)` instead of
`... (p.matched + W64 1)` (`Defs.lean:573`).

1. `MaybeDecrTo.spec` returns `progressMaybeDecrTo p rejected matchHint`; its doc comment says the
   postcondition "states the body's arithmetic verbatim". With the old body, the model changes with
   it, and the spec is provable by the same proof. Nothing at this level excludes the bug.
2. The leader's invariant `PrOk ls p` (`Defs.lean:635`): `1 ≤ Next ≤ logLast + 1`, `Match ≤
   logLast`, `PendingSnapshot ≤ logLast`. On the probe branch `rejected = Next - 1`, so the old
   `Next' = max(min(Next-1, hint+1), 1)` is between `1` and the old `Next`: `PrOk.maybeDecrTo`
   (`Defs.lean:729`) still goes through. `Match` is untouched.
3. The step in the protocol model: a rejected `MsgAppResp` is `StepC.sendApps` alone, "`Next`
   moves, `Match` does not, and the retries are `ReplOk`" (`resp_lemmas.lean:253`). A retry from
   `Next' - 1 < Match` is `AppOk` (`Protocol/Model.lean:1493`): its `index` has a term in the
   leader's log, its entries are a prefix of the log from there, its commit at most the leader's.
   Nothing mentions `Match`.

So the proof would have gone through on the pre-fix code: F−. What the report and the maintainer
expected, `Match < Next` for every tracked peer, is stated nowhere.

## Proposal

**Slug `raft-progress-match-lt-next`**: add `uint.Z p.matched < uint.Z p.next` to `PrOk`
(`Defs.lean:635`), i.e. to the leader's `PrvalsOk` carried by `ownRaftPhys`. It is kept by
`reset` (`Next = lastIndex + 1`, `Match ≤ lastIndex`), `BecomeProbe`/`BecomeReplicate`
(`Next ≥ Match + 1`), `MaybeUpdate` (`Next = max(Next, n+1)`, `Match = n`), `MaybeDecrTo` (both
branches, at the pin), `SentEntries` (`Next` only grows), and `switchToConfig`'s fresh `Progress`.
`BecomeSnapshot(i)` sets `Next = i + 1` and needs `Match ≤ i`: `maybeSendSnapshot` runs only when
`term(Next-1)` is compacted, so `Match < Next ≤ prev.index`, and `i ≥ prev.index` needs the storage
contract's `Snapshot` clause strengthened from `prev.index ≠ 0 → Index ≠ 0` to `prev.index ≤ Index`
(true of `MemoryStorage` used as documented; see `issues/raft-memorystorage-compact-without-snapshot.md`
for what happens when it is not). The pre-fix `MaybeDecrTo` fails the new conjunct on a stale
rejection with `matchHint < Match`. Cost: small (one conjunct, about ten `PrOk` lemmas in
`Defs.lean`, one storage-clause change with its `MemoryStorage` and register instances). It
documents an efficiency invariant, not a safety one; it is the only spec-level form of "no
redundant re-replication" available without a resource model.

## Files

None besides this report.
