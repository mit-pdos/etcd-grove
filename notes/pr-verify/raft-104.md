# etcd-io/raft#104: "fix panic on commit index regression"

- PR: https://github.com/etcd-io/raft/pull/104 (open), head `d9c4b3582a42571b7e5bb9216a1a54707ccc3b82`,
  one commit. Says it fixes #25 (a closed draft PR, "prevent follower panic on commit index
  regression"). In #25, tbg asked for a reproduction and proposed opt-in, event-based handling
  instead; that became issue #29.
- Verified at: fork branch `pr-raft-104-goose-lean`, commit `d9ab8730d`, which is the PR's `log.go`
  and `log_test.go` changes applied onto the pinned raft base `509271dac` (`raft37-goose-lean`:
  raft v3.7.0 plus the single-voter read-index fix). The patch applied cleanly with no conflicts and
  no rewrites, so the verified code is the PR's code. `go build ./...` and `go test .` pass on the fork.
- This repository: branch `pr-verify/raft-104`. It contains the re-translation
  (`Code/go_etcd_io/raft/v3.lean`, only `raftLog.commitTo.impl` changes), the new spec and proofs, and
  this report. `etc/goose.py --check` fails on this branch as expected, because the pin is unchanged.

## Verdict

The change is locally well-behaved, and it cannot change any execution the proof covers. Every
caller of `commitTo` passes `tocommit <= lastIndex()`. The proof derives this for every caller from
the protocol, including `handleHeartbeat` (from `heartbeat_commit_le_last`). Under that condition
the new branch is dead code, so the PR's spec is proved, it implies the old one, and every existing
raft result still holds with the same axioms. The new branch is reachable only when a follower has
lost log entries it already acknowledged, which is a durability violation. In that case the change
is unsafe. The follower marks as committed, and hands to the application, its own entries up to
`lastIndex()`, which can be an old term's entries at indices where the cluster committed different
ones: a silently divergent state machine instead of a crash. The PR also does not do what #25
proposed (reject the heartbeat so the leader lowers the follower's progress). On raft v3.7 the
follower is not repaired afterwards either. **Not sound as proposed.**

Not covered: the protocol with data loss, which is outside the model and is where the branch
lives. That part was checked with Go tests (Findings), not proofs.

## Changed functions

| Function | Kind | Before | After | Outcome |
|---|---|---|---|---|
| `(*raftLog).commitTo` (log.go) | behavior change (the out-of-range case: `Panicf` becomes `Warningf` plus a clamp to `lastIndex()`) | verified (`raftLog.commitTo.spec`, premise `tocommit <= lastIndex()`) | verified: the old spec re-proved of the new code with the proof unchanged; the new spec `specNew` proved; `spec_implies_old` | new spec, compatible (lemma); callers unaffected |

No types, struct fields or package variables change. `log_test.go` changes `TestCommitTo`'s
out-of-range case from expecting a panic to expecting a clamp to 3.

### The specs

- Old (`Spec/go_etcd_io/raft/v3/raftLog__commitTo.lean`, `raftLog.commitTo.spec`): if
  `tocommit <= lastIndex()`, then `committed := max(committed, tocommit)`
  (`plogCommitTo`). The premise is what makes the `Panicf` dead.
- New (same file, `raftLog.commitTo.specNew`): no premise, and `committed := max(committed,
  min(tocommit, lastIndex()))`. Since `committed <= lastIndex()` (part of `ownRaftLog`), the
  out-of-range case gives `lastIndex()`.
- Difference: the new spec admits any `tocommit`, and clamps instead of crashing.
  `raftLog.commitTo.spec_implies_old` (`Proof/go_etcd_io/raft/v3/raftLog__commitTo.lean`) proves
  that under the old premise the new spec gives the old postcondition.
- Proofs, in the same Proof file:
  - `wp_proof`, the old spec: unchanged; its `exfalso; word` closes the new branch as before.
  - `wp_proof_new`, the new spec: the `Warningf` goes through the `Logger` contract `isLogger`
    (a definition, not an axiom).
  - `lastIndex()` is read three times on the new path (in the condition, as the `Warningf`
    argument, and in the assignment). All three reads are on the same unchanged log.
- What the new spec cannot say at this level: whether the entries it marks committed are the
  cluster's committed entries. That is a protocol property, which the next section addresses.

## Callers (step 6)

The new spec is compatible, so no caller's obligations change. `Link.lean` still links
`raftLog.commitTo.wp_proof`, the old spec. The callers' proofs were rebuilt against the new
translation (`lake build Proof.go_etcd_io.raft.v3.Link Proof.go_etcd_io.raft.v3.Results`, 1837 jobs,
success):

- `raftLog.maybeCommit`: verified, unchanged. The premise comes from `matchTerm`.
- `raftLog.maybeAppend`: verified, unchanged. The premise holds because
  `min(committed, lastnewi) <= lastIndex()` after the append.
- `raft.handleHeartbeat` (through `Step`): verified, unchanged. The premise comes from the protocol
  fact `heartbeat_commit_le_last` (`Protocol/Facts.lean`, proved). That fact rests on the model's
  durability: a node acknowledges only entries it holds, and never loses them.
- `raft.restore`: verified, unchanged. Its fast-forward path calls `commitTo` after `matchTerm`.

The reviewer checked every caller in the Go code. In a run where acknowledgements are durable,
only `handleHeartbeat` can ever pass `tocommit > lastIndex()`: the heartbeat's commit is
`min(pr.Match, committed)`, `Match` rises only from `MsgAppResp`, and in both synchronous and
asynchronous storage modes a `MsgAppResp` goes out only after the append is durable. So the
clamp fires only after a follower lost entries it acknowledged.

## Trust base (step 7)

- No new axioms or `sorry`s.
- `#print axioms` of all of `Proof/go_etcd_io/raft/v3/Results.lean` is identical on this branch
  and on `lean` (a line-for-line `diff` of the output is empty), with no `sorryAx`.
- `wp_proof`, `wp_proof_new` and `spec_implies_old` rest on the same axioms, which are only the
  translation's axiomatized types.
- `etc/tcb-report.py` was not run because it needs a full `lake build` of the branch; the server
  proofs, which import raft, would all rebuild. The collection `etc/tcb-collections/pr-raft-104.txt`
  holds the roots, with no baseline yet.
- `etc/verified-code.py`: no change. `commitTo` is verified before and after.

## Findings

1. **The clamp commits divergent entries (a bug in the PR).** Scenario:
   - A follower holds entries 2..3 of term 1 durably.
   - It accepts the term-2 leader's entries 2..5, which overwrite them, and acknowledges index 5.
   - It then loses that write: an un-fsynced WAL tail, the case the PR's comment describes.
   - On restart its log is again 1..3 with entries 2..3 of term 1.
   - The leader heartbeats `Commit = min(Match = 5, 5)`.

   Before the PR, the follower panics. With the PR, it sets `committed = 3` and
   `nextCommittedEnts` returns entries 2..3 of term 1, while the cluster's committed entries 2..3
   are of term 2. A heartbeat carries no log check, so nothing stops this.
   - Reproduction against the PR head (upstream, gogoproto):
     `notes/pr-verify/raft-104/upstream_commit_regression_divergence_test.go.txt`, test
     `TestCommitToClampCommitsDivergentEntries`. It fails on the PR head and panics on its base.
2. **No recovery after the clamp.** The second test, `TestCommitToClampNeverRepaired`, runs the
   leader and the follower for 50 heartbeat/append rounds. Entries 2..3 stay divergent on the
   follower, which keeps acknowledging the leader. The mechanism differs by version:
   - Upstream PR head: the clamp itself prevents repair. The leader probes down to `prev = 1`,
     and the follower, whose commit index is now 3, answers it as a success. Without the clamp,
     the same test repairs the follower (reviewer's counterfactual).
   - v3.7, the verified base: the probe floor `Next >= Match + 1` keeps the leader resending
     `prev = 5` and being rejected, with or without the clamp. The lost acknowledgement leaves the
     leader's `Match` too high, and nothing lowers it.

   The v3.7 port of the test (protobuf-go v2 messages) is
   `notes/pr-verify/raft-104/fork_clamp_test.go.txt`. Raising `committed` without lowering the
   leader's `Match` therefore does not let the follower recover. #25's proposal did: answer the
   heartbeat with a rejection so the leader lowers `Match`/`Next` and probes by term.
3. **The PR's comment and title misname the cause.** Losing a persisted commit index is harmless:
   the entries are still there and the commit index is learned again. What reaches this branch is
   losing acknowledged *log entries*, a durability violation. As #25's review says, the panic is
   the assertion that catches it.
4. The change is unconditional for every user of raft, unlike #29's opt-in design.

No bug in the existing (pinned) code was found, so nothing was added to `issues/`. The behavior
under data loss is outside raft's contract, which requires storage writes to be durable before the
acknowledgement is sent.

Reviewer, fresh subagent: confirmed claims (a) to (d); corrected the v3.7 repair mechanism, now
stated in finding 2. No open points.

## Draft review comment (for the user to edit and post)

> Thanks for looking into this. I don't think clamping is safe, though. `commitTo` can only see
> `tocommit > lastIndex()` from a heartbeat, and only when this follower has lost log entries it had
> already acknowledged (the leader's `pr.Match` comes from its `MsgAppResp`). The commit index
> itself being lost would not trigger it. In that situation the entries the follower still has at
> those indices may be from an older term and differ from what the cluster committed, and heartbeats
> do no log matching. With this change the follower marks them committed and applies them.
>
> A small test: give follower 2 a storage with entries 1..3 of term 1, then step
> `MsgHeartbeat{From: 1, Term: 2, Commit: 5}`. After this change `committed` is 3 and
> `nextCommittedEnts` returns entries 2 and 3 of term 1. A term-2 leader that committed 1..5 has
> different entries there. Before the change this panics.
>
> Raising the commit index also doesn't help the leader repair the follower, since the leader still
> believes `Match = 5`. If this is to be made recoverable, I think it needs the follower to reject
> (as #25 sketched), so that the leader lowers the follower's progress and re-probes, and probably
> behind an opt-in as discussed in #29. The panic is currently what keeps a follower with a lost
> WAL tail from diverging silently.
