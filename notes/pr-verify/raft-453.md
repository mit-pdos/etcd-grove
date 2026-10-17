# etcd-io/raft#453: "raft: return error for rejected conf change"

- PR: https://github.com/etcd-io/raft/pull/453, head `d6e469644a172b0deb311205780639cb49e207c9`
  (one commit), open; it says it fixes etcd-io/raft#354 ("ConfChange silently converted to no-op
  without error notification").
- Verified at: the fork's `raft37-goose-lean` (`509271dac`) plus the PR, branch
  `pr-raft-453-goose-lean` of `~/etcd` (worktree `~/etcd-pr/raft-453`), commit `1f4e8492e`. The
  PR (`raft.go`, `raft_test.go`, `testdata/confchange_v2_add_single_explicit.txt`) applied
  cleanly: there were no conflicts and no rewrites, so the verified code is the PR's code. `go build ./...` and
  `go test ./...` pass there.
- This repository: branch `pr-verify/raft-453` (worktree `/shared/etcd-grove-pr/raft-453`).
  `Code/go_etcd_io/raft/v3.lean` was regenerated from the fork worktree (`etc/goose.py --project raft
  --src raft=...`). The pin in `etc/goose.py` is unchanged, so `etc/goose.py --check` fails on this
  branch, as it is expected to.

## Verdict

As far as `stepLeader` goes, the change does what it says, and it is safe. A proposal that is not
dropped returns `ErrConfChangeRejected` exactly when the conf-change loop refused one of its conf
changes. The batch is still appended and broadcast, with the refused change replaced by an empty
entry. Every other path is unchanged: `ErrProposalDropped` wins when the batch is also dropped, and
`nil` comes back otherwise. All of this is proved with no new axiom or `sorry`, and so are the
callers up through `RawNode` and `node.run`. The PR does **not** fix #354 for `Node` users,
etcd among them. `Node.ProposeConfChange` goes through `Node.Step`, which does not wait for the
proposal's result, so the new error is thrown away and the caller still gets `nil`; etcd's
`configure` still waits until its timeout. The new error is also returned for a whole batch whose
normal entries *were* appended, which a caller reading "error" as "nothing appended" gets wrong.

## Changed functions

| Function / item | Kind | Before | After | Outcome |
|---|---|---|---|---|
| `stepLeader` (`raft.go`, MsgProp branch) | behavior change | verified | verified | new spec, incompatible (callers checked) |
| `ErrConfChangeRejected` (new package variable) | new | n/a | in `isInitialized` | package initializer proof (`Init.lean`) extended |

Callers re-checked because the error is new (step 6):

| Caller | Before | After | Outcome |
|---|---|---|---|
| `raft.Step` | verified | verified | spec changed: `"Herr"` gains an `ErrConfChangeRejected` disjunct, compatible for every non-`MsgProp` type |
| `RawNode.ProposeConfChange` | verified | verified | spec changed (user-visible): the error may be `ErrConfChangeRejected` |
| `RawNode.Propose` | verified | verified | spec unchanged: a normal entry is never refused (proof adapted) |
| `RawNode.Step`, `Campaign`, `ForgetLeader`, `Report*`, `TransferLeader`, `ReadIndex`, `Advance`; `tickElection`, `tickHeartbeat` | verified | verified | unchanged specs, proofs unchanged (non-`MsgProp`, or the error is ignored) |
| `node.run` (`wp_rn_raft_Step_prop`, `InvNodeRun.lean`) | verified | verified | the result channel's predicate `stepErr` unchanged: a waited-on proposal is `Propose`'s normal entry |
| `node.Propose`, `node.ProposeConfChange`, `node.stepWithWaitOption` | verified | verified | specs unchanged (rebuilt) |
| etcd server (`NodeBridge.applyErrIs_of_stepErr`), the register example | verified | verified | unchanged (rebuilt; see "Builds") |

## The behavior change

- **Old** (`lean`, `Spec/go_etcd_io/raft/v3/stepLeader.lean`): a step that is not dropped returns `nil`.
- **New** (this branch, same file, `stepLeader.spec`): a step that is not dropped returns
  `ErrConfChangeRejected` (the package variable's value) if the message is a `MsgProp` and
  `LeaderPropRejects s ents c.joint`, and `nil` otherwise. `LeaderPropRejects`
  (`Proof/go_etcd_io/raft/v3/InvConfChangeMsg.lean`) says that the loop's batch, `propConf` of the
  decoded conf changes `ents.map ccOf`, differs from the proposed one. That is the same as saying
  some conf change was refused: a refused entry becomes the zero entry (`Type 0`), which a
  conf-change entry (`Type 1`/`2`) never is (`rej_zero`), and nothing else is touched (`PropRepl`).
  `LeaderStepResultC` (the state change) is unchanged.
- The old spec does not hold of the new code (a refused change now returns an error); the change is
  incompatible, so the callers were checked (above). `stepLeader.specNP` with `stepLeader.spec_np`
  restates the old shape for every type but `MsgProp`, which `Step`'s other branches use unchanged.
- `raft.Step.spec` (`Spec/go_etcd_io/raft/v3/raft__Step.lean`): the `MsgProp` disjunct of
  `"Herr"` is now `ErrProposalDropped ↦□ err ∨ (⌜role = leader ∧ LeaderPropRejects s ents c.joint⌝ ∗
  ErrConfChangeRejected ↦□ err)`. Only that implication goes up to this level (an
  `ErrConfChangeRejected` means a refusal at the leader). The converse (a refusal means the error)
  stops at `stepLeader.spec`, because `Step`'s postcondition does not expose the batch.
- `RawNode.ProposeConfChange.spec` (`Spec/go_etcd_io/raft/v3/RawNode__ProposeConfChange.lean`): the error
  is `nil`, `ErrProposalDropped` or `ErrConfChangeRejected`. It does not say *when*, because the `RawNode`
  abstraction hides the raft state; as before, `nil` does not mean accepted (a follower forwards
  and returns `nil`).

## Caller graph explored

`stepLeader` → `raft.Step` (spec changed, MsgProp only) →
- `RawNode.ProposeConfChange` (spec changed; exported API: a user-visible change, which is what the PR
  intends; the PR has no CHANGELOG entry, and raft keeps none);
- `RawNode.Propose` (absorbed: spec unchanged);
- `RawNode.Step` (absorbed: ignores the error's shape);
- `node.run` (absorbed: `wp_rn_raft_Step_prop` now returns `stepErr err ∨ (a conf entry in the batch ∗
  ErrConfChangeRejected)`; the waited path's batch is `Propose`'s one normal entry, so `stepErr`, the
  result channel's predicate, is unchanged; the forwarded path discards the error) →
  `node.Propose`, `node.ProposeConfChange` (unchanged) → the etcd server and the register example
  (unchanged).
- the other `raft.Step` callers step non-`MsgProp` messages: unchanged.

## Trust base

- No new axiom and no new `sorry`: `etc/tcb-report.py --check` still matches `etc/tcb-baseline.txt`
  (229 axioms, 12 `sorry`s, the whole repository). The PR's roots (collection
  `etc/tcb-collections/pr-raft-453.txt`: `stepLeader`, `raft.Step`, `RawNode.Propose(ConfChange)`,
  `node.run`, `node.Propose(ConfChange)`) reach no `sorry`. They rest on 13 trust-boundary axioms,
  all already there on `lean`: `DescribeConfChange`, `context.ErrDone`, `fmt.Errorf`, and the
  protobuf `proto.*` codecs (`Clone*`, `EqualConfState`, `Marshal`/`UnmarshalConfChange(V2)`,
  `SizeEntry`) and `ConfChangeType.String`.
- The package initializer proof (`Proof/go_etcd_io/raft/v3/Init.lean`) covers the new variable:
  `errors.New`'s non-`nil` result is stored and frozen (`isInitialized`'s `ErrCCRejected`).
- `disableConfChangeValidation` stays `false` (`ownRaftPhys`, as `newRaft`'s premise). With it on,
  nothing is refused and `nil` is returned, so the spec would hold, but that case is not verified.

`etc/verified-code.py --package go.etcd.io/raft/v3` reports 260 of 327 functions verified
(3111 of 3707 lines). The PR adds no function and removes none, and `stepLeader` stays verified,
so the counts are the same before and after.

## Findings

Bugs in the PR (Go tests against the PR's head, `notes/pr-verify/raft-453/pr453_findings_test.go`,
how to run it in `notes/pr-verify/raft-453/README.md`; both tests pass, which confirms the behavior):

1. **(High: the PR's purpose) `Node` users never see the error.** `node.ProposeConfChange` →
   `node.Step` → `stepWithWaitOption(ctx, m, false)`: no result channel, and `run` discards
   `r.Step`'s error. A refused conf change still returns `nil`
   (`TestPR453NodeProposeConfChangeRejectedReturnsNil`, which also shows that `RawNode.ProposeConfChange`
   does return it). etcd's `EtcdServer.configure` uses `node.ProposeConfChange`, so the hang
   described in #354's discussion (waiting on `<-ch` until the request times out) is not fixed. The
   proof shows the same: `node.ProposeConfChange.spec` and the result channel's predicate did not
   change.
2. **(Medium) The error for a batch that was appended.** A `MsgProp` with a normal entry and a
   refused conf change returns `ErrConfChangeRejected`, yet both entries (the normal one, and the
   empty replacement) are appended and broadcast (`TestPR453BatchWithRejectedConfChange`). Until now
   the only error from a proposal, `ErrProposalDropped`, meant nothing was appended; a caller that
   retries on any error duplicates the normal entries. (ahrtr's comment on #354 makes the same point
   about batching.)
3. **(Medium) `nil` still does not mean accepted.** At a follower the proposal is forwarded and
   `nil` returned. The leader's refusal is not reported back, so the error is "refused here, at the
   leader" only, which the PR's doc comment does not say.
4. **(Low) A new error from `Step` of received messages.** A `RawNode` application stepping a
   follower's forwarded `MsgProp` at the leader now gets `ErrConfChangeRejected` back, where it used
   to get `nil` or `ErrProposalDropped`.

Bugs in the existing (pinned) code: none found. The silent refusal is documented
(`Node.ProposeConfChange`: "the configuration change may be dropped with or without an error being
returned").

The reviewer subagent agreed: it found no spec bug and raised the same four points. Open: whether
`RawNode.ProposeConfChange.spec` should tie the error to the refusal. That would need the raft state
in the `RawNode`'s abstraction.

## Builds

The full `lake build` (default target, 5104 jobs) succeeds on this branch. That includes raft's
`Link`/`Results` and every consumer of raft's package facts: the register example, the etcd
server, `read`, `v3rpc` and `apply`.

## Draft review comment (for the user to edit and post)

> Thanks for picking this up. I checked the change against `stepLeader`: a proposal that isn't
> dropped now returns `ErrConfChangeRejected` exactly when one of its conf changes was refused,
> and the batch is still appended (with the refused change as an empty entry). Two things before
> this can close #354:
>
> 1. `Node.ProposeConfChange` goes through `Node.Step`, which doesn't wait for the proposal's
>    result (`stepWithWaitOption(ctx, m, false)`), so `node.run` drops the error and `Node`
>    users, etcd's `configure` included, still get `nil`. Only `RawNode.ProposeConfChange`
>    (and direct `raft.Step`) callers see the new error. If the goal is #354, `ProposeConfChange`
>    would need to wait for the result, as `Propose` does (`stepWait`). That changes its latency
>    and blocking behaviour, so it may deserve its own discussion.
> 2. For a `MsgProp` with several entries, the error is returned for the whole batch even
>    though the normal entries were appended. `ErrProposalDropped` has meant "nothing was
>    appended", so a caller that retries on error will duplicate them. A test with
>    `Entries: {{Data: "x"}, {Type: EntryConfChange}}` after a pending conf change shows it.
>    Documenting this on `ErrConfChangeRejected` ("the proposal was appended with the refused
>    conf change replaced by an empty entry; other entries of the batch were appended") would
>    help, as would noting that it is only returned at the leader (a follower forwards the
>    proposal and returns `nil`).
