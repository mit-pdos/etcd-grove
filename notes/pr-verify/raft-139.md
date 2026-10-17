# etcd-io/raft#139: "raft: advance commit index safely"

- PR: https://github.com/etcd-io/raft/pull/139 (open, "needs rebase", marked as blocked by the
  author on #145), head `4e08f525c` (two commits: `87ac09e77` "advance commit index safely",
  `4e08f525c` "pass the leader term to append/commit methods"), base `026484c68`.
- Verified at: branch `pr-raft-139-goose-lean` of the Goose fork, commit `1daf55cb3` (= the pinned
  `raft37-goose-lean` `509271dac`, raft v3.7.0 plus the single-voter read-index fix, with the PR
  applied); this repository's branch `pr-verify/raft-139` (worktree `../etcd-grove-pr/raft-139`).
- Files the report relies on: `notes/pr-verify/raft-139/` (README.md lists them).

## Verdict

The change is safe as far as it was verified: with it, every `raft.Step` still refines the protocol
model, and the protocol's safety results (log matching, leader completeness, state machine safety,
read-index) go through unchanged, with no new axiom or `sorry`. The model had to be generalized so
that a follower may *skip* a commit (on a heartbeat, on an accepted `MsgApp`, on a snapshot whose last
entry it already has): the PR commits less, never more, than the code it replaces. The panic it
removes (`commitTo` past the end of the log) was already unreachable in the verified protocol
(`heartbeat_commit_le_last`); the proof no longer needs that fact for `handleHeartbeat` to be safe.

What is not covered, and what the proof does not show:
- The PR's own argument ("`leaderTerm = T` means my log is a prefix of leader `T`'s") is not stated or
  proved: commits are still justified by the old protocol facts. A future change that relies on it
  (the PR's TODO of dropping `min(committed, lastnewi)`) would need that ghost invariant.
- Liveness. The PR makes followers commit later in some cases, and in one case
  (`TestReviewSnapFastForwardStall`) a follower stays behind until the application calls
  `ReportSnapshot` (etcd does; an application that does not stalls that follower).
- Two new ways to go wrong on inputs the verified protocol never produces, recorded as premises:
  `append` silently drops a leader's own entries when the storage's last entry is of a term above
  the persisted `HardState.Term`, and a `MsgApp` with an entry of a term above the message's now
  panics.

## The port onto the verified base

The PR is against raft before #145 (`logSlice`) and gogoproto `raftpb`; the base is v3.7.0 (protobuf-go
v2, pointer messages with getters, `maybeAppend(a logSlice, committed)`). The non-test changes were
re-applied by hand, in the base's style:
- `maybeAppend`'s leader term is `a.term` (the PR's new first parameter `leaderTerm`; `a` is
  `logSliceFromMsgApp(m)`, whose `term` is `m.Term`), so `maybeAppend` keeps its signature;
- `maybeCommit(leaderTerm, at entryID)` (the base's `at` replaces `(maxIndex, term)`);
- `handleHeartbeat` / `handleSnapshot` read `m.GetTerm()`; `append`'s last-entry check reads
  `GetTerm()`; `newLogWithSize` builds the struct literal with `leaderTerm: lastTerm`.
No conflict needed a choice that changes behaviour. The PR's test changes were ported where they
apply; four base tests (newer than the PR) needed adapting to the new invariant
(`TestIsOutOfBounds`, `TestTerm`, `TestSlice`, `TestScan`: append at a leader term at least the
entries'; `TestLogMaybeAppend`: the log's leader term equal to the slice's;
`TestLeaderIncreaseNext`: a node whose term is below its log's leader term drops its own appends,
so the test first moves it to term 3). `go build ./...` and `go test ./...` pass.

## Changed functions

All of them were verified before (in `lean`'s `etc/link-lean-first-raft.txt`); all are verified
after. "new spec" means the statement changed; the old one is in `lean` (`git show lean:<file>`).

| Function | Kind | Outcome |
|---|---|---|
| `raftLog.commitTo` | behavior change | new spec, no premise (`Spec/.../raftLog__commitTo.lean`); old premise `tocommit ≤ lastIndex` gone; equals the old post at the log's leader term (`logCommitTo_at_term`) |
| `raftLog.append` | behavior change | new spec (`logAppendAt`): no-op for an outdated leader term, sets `leaderTerm`; new premise: last entry's term ≤ leader term |
| `raftLog.maybeAppend` | behavior change | new spec: outdated leader → `(0,false)`; `leaderTerm` moves to `a.term` iff something was appended; commit only at the new leader term; new premise: no entry above `a.term` |
| `raftLog.maybeCommit` | behavior change | new spec: commits iff guard ∧ `lt = leaderTerm`; result still the guard |
| `newLogWithSize` | behavior change | new post: `leaderTerm` = last stored entry's term (reads `Storage.Term(lastIndex)`) |
| `raft.handleHeartbeat` | behavior change | new spec, premise `m.Commit ≤ lastIndex` removed; commit `logCommitTo s m.Term m.Commit` |
| `raft.handleAppendEntries` | behavior change | new spec (`HandleAppResult`); new premises `leaderTerm ≤ m.Term`, entries' terms ≤ `m.Term` |
| `raft.restore` | behavior change (new parameter) | new spec: fast-forward commits only at the log's leader term |
| `raft.handleSnapshot` | behavior change | new spec: fast-forward as `restore`, the reply carries the commit index; after a restore `leaderTerm := m.Term` |
| `raft.appendEntry` | behavior change | new spec: post `logAppendLT` (sets `leaderTerm := r.Term`); new premise `leaderTerm ≤ term` |
| `raft.becomeLeader` | behavior change | new spec: `becomeLeaderLog` at `logAppendLT` (leader term = term); new premise `leaderTerm ≤ term` |
| `raft.maybeCommit` | refactor (same post) | old post re-proved under the new premise `leaderTerm = term` |
| `RawNode.Bootstrap` | refactor | old spec re-proved (`append(1, ...)`) |

Changed type: `raftLog` gains `leaderTerm`; `LogState` gains `leaderTerm` and `ownRaftLog` relates it
to the field (`Proof/go_etcd_io/raft/v3/InvRaftlog.lean`, `Hlt`).

### The old and new specs in a sentence

- `commitTo`: was "with `tocommit ≤ lastIndex`, `committed := max(committed, tocommit)`"; now
  "always returns; `committed := max(committed, min(tocommit, lastIndex))` if `lt = leaderTerm`,
  else unchanged" (`logCommitTo`, `InvRaftlog.lean`). Not compatible (a commit can be skipped).
- `append`: was "splice the batch" (`logTruncateAppend`); now "the same at `leaderTerm := lt` when
  `lt ≥ leaderTerm` and the batch is non-empty, else nothing" (`logAppendAt`).
- `maybeAppend`, `handleAppendEntries`: was "on a match, commit `min(committed, lastnewi)`"; now "an
  outdated leader is refused as a mismatch; on a match the commit happens only if the log's leader
  term is then `m.Term`, which it is whenever anything was appended".
- `handleHeartbeat`: was "commit `m.Commit` (premise: within the log)"; now "commit
  `min(m.Commit, lastIndex)` at the log's leader term, nothing otherwise" (no premise).
- `restore`/`handleSnapshot`: the fast-forward path commits only at the log's leader term; a restore
  sets the leader term to the message's.

## Callers (step 6)

The incompatible changes are all "a commit may be skipped". They were followed to the protocol:
- **The model** (`Protocol/Model.lean`, `StepC.lean`, `StepR.lean`, `StepLemmasR.lean`): the rules
  `heartbeat`, `appAccept` and `snapFastfwd` take a flag `cm : Bool`; with `cm = false` the
  follower's commit index is unchanged (and `snapFastfwd`'s reply carries it; `appAccept` requires
  `cm = false → plogFindConflict = 0`, i.e. nothing was appended). The ghost refinement
  (`Refinement.lean`: `ownRaftGhost_step_heartbeat` at any commit target `K ∈ {m.commit, 0}`,
  `ownRaftGhost_step_app_accept` at any `K ≤ min(m.commit, lastnewi)`, `snapFastfwd` with `cm = false`
  reusing the stale-snapshot lemma), the dynamic refinement (`RefinementDyn.lean`) and the
  reconfiguration invariant (`StepRInv.lean`: `RInv_appAccept` at any such `K`, exact at a
  conflict) are re-proved. No protocol result changed statement.
- **`NStateWf`** (`Defs.lean`) gains `LtInv`: `leaderTerm ≤ term`, and a leader's `leaderTerm = term`.
  It holds at `Step` boundaries (not inside `ownRaftPhys`: inside `becomeLeader`, between the role
  store and the append, and inside `becomeFollower`, between `reset`'s term store and the role store,
  it does not). It is what makes the new early returns of `maybeAppend`/`append` dead
  (`handleAppendEntries`, `appendEntry`) and the leader's `maybeCommit` commit exactly as before.
- Caller graph re-checked, each now proved: `stepFollower`, `stepCandidate` (new premise
  `leaderTerm ≤ term`), `stepLeader` (new premise `leaderTerm = term`, through
  `wp_stepLeader_prop`/`_appresp`), `switchToConfig`, `applyConfChange` (new premise at a leader),
  `raft.Step` (every branch: `MsgApp`, `MsgHeartbeat`, `MsgSnap`, the votes and responses through
  `NStateWf`), `RawNode.Tick`, `acceptReady`, `ApplyConfChange`, `Bootstrap`, the node run loop
  (`InvNodeRun`). New protocol fact: `app_entries_term_le` (`Protocol/Facts.lean`: a received
  `MsgApp`'s entries are of terms at most the message's, from the sender's `lpfull`).
- **Exported API**: `newRaft` (and so `NewRawNode`'s callers) gains the premise "the last stored
  entry's term ≤ `HardState.Term`" (`Spec/go_etcd_io/raft/v3/newRaft.lean`), which `NewRawNode`
  discharges (an empty storage). It is true of every storage raft wrote (the `HardState` is
  persisted with the entries; etcd's WAL does that) and false of a storage with entries and no
  (or an older) `HardState`. The PR does not document it.

## Trust base

No new axiom, no new `sorry`. After a full `lake build` of this branch (5104 jobs, successful),
`etc/tcb-report.py --check` matches `etc/tcb-baseline.txt` unchanged (229 axioms, 12 `sorry`s, none of
them reached by raft), and the collections `raft.txt` (13 axioms, 0 `sorry`s), `server-raft.txt`
(6, 0) and `register.txt` (13, 10) match their `lean` baselines. The new collection
`etc/tcb-collections/pr-raft-139.txt` (the changed functions and the callers re-checked) rests on 10
axioms, all existing raft trust-boundary axioms (`DescribeConfChange`, `fmt.Errorf`,
`proto.Clone{ConfState,Entry,Snapshot}`, `proto.EqualConfState`, `proto.SizeEntry`,
`proto.UnmarshalConfChange(V2)`, `raftpb.ConfChangeType.String`), and on no `sorry`.
The new premises are the ones listed above: `newRaft`'s "last stored term ≤ `HardState.Term`"
(discharged by `NewRawNode` for an empty storage), and, internal to the proof, `LtInv` at `Step`
boundaries (proved), `app_entries_term_le` (proved).

## Findings

In the PR (Go tests in `notes/pr-verify/raft-139/`, run at the PR head and the base):
1. **Snapshot fast-forward skipped, follower can stall** (liveness). A follower that already has the
   snapshot's last entry, whose log's leader term is older than the sender's, skips the commit and
   replies with its old commit index; the leader's progress stays in `StateSnapshot`
   (`TestReviewSnapFastForwardStall`, `TestProbeSnapshotFastForwardSkipped`). Committing the
   snapshot's index there is safe whatever the leader term (it is committed and the logs match);
   the base did it.
2. **An append with nothing new commits nothing** when the log's leader term is older than the
   message's (`TestReviewNoConflictAppendNoCommit`). Safe; the commit catches up with the leader's
   first entry of its term. (`min(committed, lastnewi)` would be safe to commit there.)
3. **Silent drop of the leader's own entries** when the storage's last entry is of a term above the
   persisted term (`TestProbeLeaderEmptyEntryDropped`): `append(r.Term, ...)` returns early,
   `appendEntry` still reports the batch accepted and self-acknowledges it. Only a storage that
   violates the `newRaft` premise above reaches it; a loud failure would be better than a silent
   one.
4. **New panic on a malformed `MsgApp`** (an entry of a term above the message's,
   `TestProbeMsgAppEntryAboveMsgTerm`). The verified protocol never sends one
   (`app_entries_term_le`).
5. The new outdated-leader guards in `maybeAppend`/`append` can never fire at a `Step` boundary
   (`LtInv`); they are defence only, and if one did fire on a matching append the follower would
   reply with a rejection the model does not allow.

In the existing (pinned) code: none found.

In this repository's specs: none; the old `handleHeartbeat` premise and `heartbeat_commit_le_last`
stay (the model's heartbeat rule still states its commit against them).

Reviewer (a fresh subagent): no safety bug; findings 1–5 above are its and ours; its open point is
the first item of "what the proof does not show".

## Draft review comment

> I looked at this change against a formal model of raft (protocol and implementation). It is safe:
> the follower now commits a subset of what it committed before, and the existing safety argument
> still covers every commit it makes. Three things you may want to consider:
>
> 1. In `restore`, when the log already has the snapshot's last entry, the commit index is no
>    longer fast-forwarded unless `leaderTerm == m.Term`, and the reply then carries the old commit
>    index. The snapshot is committed and the logs match up to it, so committing it is safe at any
>    leader term. As it is, the leader's progress for that follower stays in `StateSnapshot` until
>    the application reports the snapshot (a test reproducing this is attached).
> 2. `append(leaderTerm, ...)` returns without appending when `leaderTerm < l.leaderTerm`. For the
>    leader's own `appendEntry` this is reachable only with a storage whose last entry's term is
>    above the persisted `HardState.Term`, but then `appendEntry` reports the proposal accepted and
>    self-acks it. A panic (or an assertion in `newRaft` that the last entry's term is at most the
>    `HardState`'s term) would make that misuse visible.
> 3. A `MsgApp` whose entries have a term above `m.Term` now panics in `append`. A correct leader
>    never sends one; if the intent is to validate incoming messages, rejecting it (or validating
>    the `logSlice` up front, as the TODO says) may be preferable to a panic.
