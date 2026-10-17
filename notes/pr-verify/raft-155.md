# etcd-io/raft#155: log: clean-up log conflict search

- PR: https://github.com/etcd-io/raft/pull/155 (open), head `85f43e65740047a9ff7301c9580d67b4b62b02df`
  (three commits: a test clean-up, `17f5596af` "log: clean-up log conflict search", `85f43e657`
  "log: consolidate the commited entry rewrite check").
- Verified at: fork `upamanyus/etcd` branch `pr-raft-155-goose-lean`, commit `9e87f483a` (not
  pushed), which is the PR's `log.go`/`log_test.go` diff (from its merge base `59637807b` with
  upstream `main`) applied to `raft37-goose-lean` `509271dac`, the pinned raft v3.7.0 plus the
  read-index fix. This branch: `pr-verify/raft-155` (worktree `/shared/etcd-grove-pr/raft-155`).
  The pin in `etc/goose.py` is left as it is, so `etc/goose.py --check` fails on this branch by
  design.

## Verdict

The PR is a sound refactor **for well-formed appends**. The new `maybeAppend` meets exactly the
spec the old one was proved to meet: same result, same new log, same commit index, same
ownership of the batch. The same goes for `append`. So no caller is affected:
`handleAppendEntries`, `appendEntry` and `Bootstrap` build unchanged, and so does the whole
raft proof (`Link`, `Results`).

The panic the PR removes from `maybeAppend` is `append`'s panic under the same condition, as
the PR says. The new `findConflict` does what its new doc comment says, including the range
guarantee, which is proved as a lemma.

No axiom or `sorry` was added.

What is not covered: appends whose entries are not contiguous after `prev`. The spec assumes
them away, and nothing on the `MsgApp` path checks them. On such inputs the PR changes
behavior: one case goes from a no-op to truncating the log and acknowledging an index the
node no longer has, others go from accepted to a runtime panic (Findings, below). A correct
leader never sends these, so this is not a bug under raft's fault model. It is still the one
thing worth raising on the PR.

## Applying the PR

The PR is against gogoproto raftpb (`[]pb.Entry`, field access). The pin uses protobuf-go v2
(`[]*pb.Entry`, getters). The conflicts and how they were resolved, without changing the PR's
behavior:

| File | Conflict | Resolution |
|---|---|---|
| `log.go` `append` | `ents[0].Index` vs the base's `ents[0].GetIndex()`, and `...pb.Entry` vs `...*pb.Entry` | the PR's check `first := ents[0].GetIndex(); first <= l.committed`, signature as the base |
| `log.go` `findConflict` | `pbEntryID(&s.entries[i])` | `pbEntryID(s.entries[i])` (the entries are already pointers) |
| `log_test.go` `TestFindConflict` | `[]pb.Entry`, `pbEntryID(&previousEnts[i])` | `[]*pb.Entry`, `pbEntryID(previousEnts[i])` |

`maybeAppend` applied cleanly. No upstream commits were missing. `go build ./...` and
`go test ./...` pass in the fork worktree, including the PR's new `TestFindConflict` cases.

## Changed functions

| Function (`go.etcd.io/raft/v3`) | Kind | Before (`lean`) | After | Outcome |
|---|---|---|---|---|
| `raftLog.findConflict` | behavior change (signature: `[]*Entry → uint64` became `logSlice → (entryID, bool)`) | verified | verified | new spec, incompatible (only caller `maybeAppend`, checked) |
| `raftLog.maybeAppend` | refactor | verified | verified | old spec re-proved, statement unchanged |
| `raftLog.append` | refactor (panic check `ents[0].Index-1 < committed` became `ents[0].Index <= committed`; new message) | verified | verified | old spec re-proved, proof unchanged |
| `logSlice.lastIndex` (`types.go`, unchanged; a new callee of verified code) | new to the proof | translated | verified | new spec (`s.prev.index + len(s.entries)`) |

No types, struct fields or package variables change. Invariants are unchanged.

`etc/verified-code.py --package go.etcd.io/raft/v3` (worktree, `--reuse`) gives 261 of 327
functions verified. The difference from `lean` is `logSlice.lastIndex`, from translated to
verified. The line numbers it prints are those of the pinned source, not of the PR.

## The behavior change: `findConflict`

- **Old** (`lean:Spec/go_etcd_io/raft/v3/raftLog__findConflict.lean`): takes a batch of entries
  and returns `plogFindConflict`, the index of the first entry the log does not have, or `0`
  if it has them all. The premise is that every entry is at or above the compaction boundary.
- **New** (`Spec/go_etcd_io/raft/v3/raftLog__findConflict.lean`): takes a log slice `s` and
  returns `(m, ok)`:
  - `ok` is whether the log has `s.prev`;
  - if it does, `m = plogFindMatch …`, the id of the last entry of `s` the log has before the
    first one it lacks (`s.prev` if the first entry already mismatches);
  - otherwise `m` is `entryID{}`.

  The premise is that `s` is well-formed (`PlogWf s.prev ents`: contiguous indices after
  `s.prev`).
- What the doc comment promises is `plogFindMatch_drop` (`Proof/go_etcd_io/raft/v3/Plog.lean`).
  For a well-formed slice:
  - `m.index = s.prev.index + k` with `k ≤ len(s.entries)`;
  - if `s.prev` is in the log, so is `m`, and so is every entry up to it;
  - the entries after `m` start at the first one the log lacks.

  It also ties the new function to the old one. `plogFindConflict` (the old function's
  result) is `0` exactly when nothing is left after `m`, and is otherwise the index of the
  first entry left. This is what lets `maybeAppend` keep its spec.

The function is new in shape, so its spec could not hold of the old code, which had a
different signature. The difference from the old spec is the `prev` check, moved in from
`maybeAppend`, and returning the last match instead of the first conflict.

## The refactors

- `raftLog.maybeAppend` (`Spec/go_etcd_io/raft/v3/raftLog__maybeAppend.lean`): the statement is
  identical to `lean`'s (`git diff lean` touches only the doc comment). The proof
  (`Proof/go_etcd_io/raft/v3/raftLog__maybeAppend.lean`) now follows the fast-forward:
  - `findConflict`'s new spec;
  - the sub-slice `a.entries[k:]`, whose bounds hold by `plogFindMatch_drop`;
  - `append` of that sub-slice, which is empty when the log has every entry; then `append`
    returns at once and the log is unchanged;
  - `logSlice.lastIndex` twice;
  - `commitTo`.

  The old premise (the conflict index is `0` or above `committed`) becomes `append`'s
  `committed < ents[0].Index`, because the first entry left is the old conflict index. That
  is the PR's claim that the removed panic is redundant, made exact. The batch's capacity is
  handed to `append` in the same way as before, and in the adopt case it is the same suffix
  of the same backing array.
- `raftLog.append`: the proof is unchanged. The new check `first <= committed` and the old
  `first - 1 < committed` agree for `first ≥ 1`. At `first = 0` the old one wrapped and passed,
  and the new one panics. Every caller passes indices `≥ 1` (`appendEntry`: `lastIndex + 1 + i`;
  `Bootstrap`: from 1; `maybeAppend`: `prev.index + 1 + k`), and the spec's premise
  `committed < ents[0].Index` excludes both.

## Callers (step 6)

```
findConflict (new spec) ── maybeAppend (only caller; Go grep of every raft package) ── re-proved, spec unchanged: stop
append (spec unchanged) ── maybeAppend, raft.appendEntry, RawNode.Bootstrap: rebuilt unchanged
maybeAppend (spec unchanged) ── raft.handleAppendEntries: rebuilt unchanged
logSlice.lastIndex (new spec) ── maybeAppend
```

No exported API changes behavior for well-formed input.

## Trust base

`etc/tcb-report.py --collection etc/tcb-collections/pr-raft-155.txt` (roots: the four functions
above, `handleAppendEntries`, `appendEntry`, `Bootstrap`; full worktree build) shows:

- **`sorry`s**: none.
- **Axioms reached**: `findConflict`, `maybeAppend`, `append` and `logSlice.lastIndex` reach
  none.
- **The callers' axioms**: `appendEntry` and `Bootstrap` rest on five pre-existing
  trust-boundary axioms (`fmt.Errorf`, `proto.CloneEntry`, `proto.CloneSnapshot`,
  `proto.SizeEntry`, `raftpb.ConfChangeType.String`). `handleAppendEntries` rests on none.

This work added no postulate and no `sorry`. `etc/tcb-report.py --check` matches
`etc/tcb-baseline.txt` (229 axioms, 12 `sorry`s, unchanged). The `raft` collection matches its
baseline (13 axioms, 0 `sorry`s, unchanged).

## Findings

**In the PR: behavior on malformed appends.** These are outside the spec's premise, which
assumes the leader sends contiguous entries. Nothing validates them:
`logSliceFromMsgApp`'s TODO says so, and `logSlice.valid` is never called on this path. The
PR's comment "prev.index <= match.index <= a.lastIndex(), so the sub-slicing is safe" holds
only for valid slices. Each case was reproduced with a Go test against the fork commit and
against its parent: `raft-155/log_malformed_append_test.go`, with its outputs
`raft-155/output-new.txt` and `raft-155/output-old.txt` (see `raft-155/README.md`).

1. **Duplicate index.** Local log 1..10, all term 1, committed 3; append `prev=(1,5)`, entries
   at indices `6, 6`, term 1.
   - Old: no conflict, nothing written; returns `(7, true)` and the log keeps 1..10.
   - New: `match = (1,6)`, then `append([6])` truncates 7..10. It returns `(7, true)`, but
     `lastIndex()` is 6, so the node acknowledges index 7, which it no longer has. With a
     `Commit` of 7 or more, `commitTo(7)` would panic.
2. **Gap.** Log 1..3; append `prev=(1,1)`, entries at `2, 5`.
   - Old: `Panicf("index, 3, is out of range [2]")`.
   - New: `unstable.slice[1,5) out of bound [1,4]` panic. Both panic.
3. **Entry below prev.** Log 1..3; append `prev=(1,2)`, entry at `1`.
   - Old: no conflict; returns `(3, true)`.
   - New: `match.index - prev.index` wraps, and a runtime `slice bounds out of range` panic
     follows.

The minor one: with a custom `Logger` whose `Panicf` returns, the old code skipped the append
of a batch that rewrites a committed entry. The new code goes on into `truncateAndAppend`,
because `append`'s `Panicf` does not stop it. The default and zap loggers panic.

**In the existing code:** none found (nothing new for `issues/`).

**The reviewer's points:** all resolved. The reviewer was a fresh subagent given the diff,
the old and new specs and the proofs. It found no soundness problem. Its documentation points
were fixed:
- the `PlogWf` premise is now documented as an assumption, not a check;
- the stale comment in `raft__handleAppendEntries.lean` is fixed;
- the "every entry up to `m` matches" promise is added to `plogFindMatch_drop`;
- the `ok = false` id is pinned to `entryID{}`.

Its malformed-input cases are the findings above.

## Draft review comment (for the user to edit and post)

> I checked this against the previous `maybeAppend` and it is equivalent whenever the appended
> entries are contiguous after `prev`. You get the same returned index, the same truncation
> point, the same commit index, and the same slice handed to `append`. The removed panic is
> indeed `append`'s under the same condition.
>
> One thing I noticed: the old code was more forgiving of a malformed `MsgApp`. Take a log at
> 1..10 (committed 3) and an append with `prev=(1,5)` and two entries both at index 6. Before
> this change it was a no-op that returned 7. Now it fast-forwards to 6, `append` truncates
> 7..10, and the node still replies with index 7, which it no longer has. An entry below
> `prev` (e.g. `prev=(1,2)` with an entry at index 1) now underflows `match.index-a.prev.index`
> and panics on the slice, where it used to be accepted. A correct leader never sends these,
> so this may well be fine. But the `NB: ... the sub-slicing is safe` comment depends on the
> slice being valid, which nothing on this path checks yet (cf. the TODO in
> `logSliceFromMsgApp`). Would it be worth validating the slice (`a.valid()`) before
> `maybeAppend`, or at least noting the assumption in the comment?
