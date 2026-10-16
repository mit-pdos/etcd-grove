# etcd-io/raft#292: decouple raftLog, phase 1 (`controlflowLog`)

- PR: https://github.com/etcd-io/raft/pull/292, "decouple raftLog - phase 1: introduce the new type
  controlflowLog" (open, for etcd-io/raft#142), head `1368b97ad8d3aa0a0eb263396ba75fe3feb875ff`,
  one commit, `log.go` only (+13 -6). Its base is `d708de9f1` (April 2025), an ancestor of the
  verified raft. It also merges cleanly with today's `raft-upstream/main` (`638f42739`).
- Verified at fork commit `1a63011bf` (branch `pr-raft-292-goose-lean` of `~/etcd`, worktree
  `~/etcd-pr/raft-292`). That commit is the PR's non-test diff applied to the pinned raft
  `509271dac` (`raft37-goose-lean`) with `git apply -3`. It applied cleanly: there were no
  conflicts and no rewrites, so the verified Go code is exactly the PR's.
  `go build ./...` and `go test` pass for `.`, `tracker`, `quorum` and `confchange` (go1.27.1).
- This repository: branch `pr-verify/raft-292`, worktree `/shared/etcd-grove-pr/raft-292`.

## Verdict

The PR is a pure refactor, and the proofs confirm it. Every existing spec of the affected functions
holds, unchanged, of the new code. These are the 33 raft functions whose Goose translation changes
(every `raftLog` method that reads a moved field, and the `raft`/`RawNode` code that reads
`r.raftLog.committed`/`applied`). The full `lake build` passes. The trust base is unchanged: no new
axiom, no new `sorry`, and `etc/tcb-report.py --check` and the `raft` collection match their
baselines. No spec changed. The only proof change is the field path in the `raftLog` ownership
predicate. The verification covers the functional behavior of raft's verified code (the specs over
`LogState`). It does not cover `raftLog.String` (untranslated formatting, unspecified) or the tests.

## What the PR changes

At the Go level, one type and one function change:

- type `raftLog`: the fields `committed`, `applying`, `applied`, `logger`,
  `maxApplyingEntsSize`, `applyingEntsSize` and `applyingEntsPaused` move into a new struct
  `controlflowLog`, which is embedded (anonymously) in `raftLog`. Go promotes the fields, so every
  `l.committed` in the source stays as written.
- `newLogWithSize`: its composite literal builds the embedded `controlflowLog{...}`, with the
  same values as before.

In the translation, every promoted access becomes an explicit two-step field reference,
`StructFieldRef controlflowLog "committed" (StructFieldRef raftLog "controlflowLog" l)`. So the
translated bodies of 34 functions change, although their Go source does not.

| Function | Kind | Before (lean) | After | Outcome |
|---|---|---|---|---|
| `newLogWithSize` | refactor (Go body changed) | verified | verified | old spec re-proved, proof unchanged |
| `raftLog.{acceptApplying, append, appliedTo, commitTo, findConflict, hasNextCommittedEnts, lastEntryID, maxAppliableIndex, maybeAppend, maybeCommit, mustCheckOutOfBounds, nextCommittedEnts, restore, slice, zeroTermOnOutOfBounds}` (15) | refactor (translation only) | verified | verified | old spec re-proved; `hasNextCommittedEnts`, `maybeAppend`, `nextCommittedEnts` and `restore` needed a renamed projection |
| `raft.{appliedTo, committedEntryInCurrentTerm, handleAppendEntries, handleSnapshot, hardState, hasUnappliedConfChanges, loadState, maybeSendAppend, maybeSendSnapshot, restore, sendHeartbeat}`, `newRaft`, `getBasicStatus`, `sendMsgReadIndexResponse`, `stepLeader`, `RawNode.Bootstrap` (16) | refactor (translation only) | verified | verified | old spec re-proved; `handleAppendEntries`, `handleSnapshot`, `maybeSendAppend`, `sendHeartbeat` and `stepLeader` needed a renamed projection |
| `raftLog.String` | translation only | translated, no spec | same | not specified (debug formatting) |
| `extend` | translation only (doc comment position) | verified | verified | unchanged |

Changed types: `raftLog` and the new `controlflowLog`. The new type has generated points-to and
field-access instances (`GeneratedProof/go_etcd_io/raft/v3/chunk2.lean`). Regenerating also
re-split the generated files, adding a new `chunk5.lean`.

There are no behavior changes, so no new specs, no `spec_implies_old` lemmas, and no caller
propagation (step 6 of the procedure). Every spec is unchanged, so every path stops at its first
node.

## The proof changes

All of these are mechanical (`git diff lean -- Proof Spec`):

- `ownRaftLog` (`Proof/go_etcd_io/raft/v3/InvRaftlog.lean`), and with it `ownRaftLog_intro` and
  `ownRaftLog_struct`: each `lv.X'` for a moved field becomes `lv.controlflowLog'.X'`. Every
  conjunct is kept, under the same name and about the same field. This is the invariant over the
  changed struct. It changes only in the path.
- `ownRaftLog_setCommitted`, `RawNode.Bootstrap`'s raw store: the store address is now
  `(l.[raftLog, "controlflowLog"]).[controlflowLog, "committed"]`.
- `raftLog__restore.lean`: the record update `{ lv with committed' := … }` becomes
  `{ lv with controlflowLog'.committed' := … }`.
- Eight proofs (`raftLog__{hasNextCommittedEnts,maybeAppend,nextCommittedEnts}`,
  `raft__{handleAppendEntries,handleSnapshot,maybeSendAppend,sendHeartbeat}`,
  `stepLeader/{MsgProp,Rest}`) rename projections the same way.

`wp_auto` handled the nested field references with no change: the generated `AccessStrict`
instances compose, as they already did for `l.unstable.offset`.

## Trust base

- `etc/tcb-report.py --check`: matches `etc/tcb-baseline.txt` (229 axioms, 12 sorries, the same as
  on `lean`).
- `--collection etc/tcb-collections/raft.txt --check`: matches (13 axioms, 0 sorries).
- New collection `etc/tcb-collections/pr-raft-292.txt` (the affected functions' specs): 10 axioms,
  0 `sorry`s, all of them already on `lean`. These are the trust-boundary specs of
  `DescribeConfChange`, `fmt.Errorf`, protobuf-go's `proto.{CloneConfState, CloneEntry,
  CloneSnapshot, EqualConfState, SizeEntry, UnmarshalConfChange, UnmarshalConfChangeV2}` and
  `raftpb.ConfChangeType.String`. This work added none.
- `etc/verified-code.py --package go.etcd.io/raft/v3`: package `go.etcd.io/raft/v3` has 189 of
  244 functions verified (2318 of 2723 lines, 85.1%), both before and after.

## Findings

- PR bugs: none. The reviewer subagent found no issue. Field promotion is unambiguous:
  `unstable.logger` sits behind a named field, `controlflowLog` has no methods, and no `raftLog`
  method shares a name with a moved field. The only `raftLog{...}` literal, in `newLogWithSize`
  in the fork and in upstream `main` alike, is the one the PR rewrites. `applyingEntsSize` and
  `applyingEntsPaused` are still zero-initialized, which the proved spec of `newLogWithSize`
  confirms (`apsize = 0`). Ownership and concurrency are unchanged: the struct is inline in the
  `*raftLog` the raft goroutine owns.
- Bugs in the existing code: none found (nothing added to `issues/`).
- Open design points (nits, from the review; not correctness):
  - Issue #142 is about *flow control*, but `controlflowLog` reads as *control flow*. A name like
    `applyState` or `applyFlowControl` would fit better.
  - `committed` is log metadata, not apply flow control: `maybeAppend`, `append` and `restore`
    check truncation against it. `logger` is not flow control either, and `raftLog` itself uses
    it heavily. Phase 2 will have to reach both through the new struct, or duplicate them.
  - While the struct is embedded, nothing is decoupled yet. A sketch of phase 2's interface would
    make phase 1 easier to judge.
  - The comment `// type embedding of controlflowLog` restates the code. It could say what the
    struct holds and why.

## Draft review comment (for the user to edit and post)

> I checked this against the raft code paths that read the moved fields: the `raftLog` methods
> and the `raft`/`RawNode` code that reads `raftLog.committed`/`applied`. The change preserves
> behavior. Promotion is unambiguous: `unstable.logger` sits behind a named field and the new type
> has no methods. The only composite literal is the one in `newLogWithSize`, and
> `applyingEntsSize`/`applyingEntsPaused` stay zero there.
>
> A few questions on the split itself:
> - #142 talks about flow control; `controlflowLog` reads as "control flow". Would something like
>   `applyFlowControl` (or `applyState`) be clearer?
> - `committed` bounds what the log may truncate (`maybeAppend`, `append`, `restore` all check it),
>   and `logger` is used by most `raftLog` methods. Should those two stay on `raftLog`, with the
>   new struct holding only `applying`/`applied` and the applying-size budget?
> - Since the embedding keeps every access as it was, this phase alone doesn't decouple anything
>   yet. Could you sketch what phase 2's interface looks like, so the split can be judged here?
> - Nit: the `// type embedding of controlflowLog` comment could say what the struct is for.
