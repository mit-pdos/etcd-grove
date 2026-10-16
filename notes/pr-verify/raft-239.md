# etcd-io/raft#239: make `StepDownOnRemoval` the default behavior

- PR: https://github.com/etcd-io/raft/pull/239, "breaking: Make `StepDownOnRemoval` the default
  behavior", open, head `d96366fd4d69691369a5e334284f265972631a6f` (one commit, base
  `d155efc81`). Implements etcd-io/raft#83.
- Verified at: fork branch `pr-raft-239-goose-lean`, commit `0a099f0cc` (worktree
  `~/etcd-pr/raft-239`), which is the pinned `raft37-goose-lean` `509271dac` plus the PR.
- Proof branch: `pr-verify/raft-239` (worktree `/shared/etcd-grove-pr/raft-239`).

## Verdict

The change is sound as far as it was verified. With the PR, `switchToConfig`'s proved spec
covers a removed or demoted leader at every `Config`: it always steps down
(`becomeFollower(r.Term, None)`), and nothing else about the function changes. Before the PR the
same spec needed the premise `Config.StepDownOnRemoval = true`. So the new spec is the old one
minus a premise, and the callers' specs lose the premises that only passed it on:
`applyConfChange`, `RestartNode` in the dynamic mode, and `newRaft`/`NewRawNode`/`Bootstrap`
through `rawNodeFresh`. Every proof was re-proved with no new axiom or `sorry`. The full trust
base is unchanged (229 axioms, 12 `sorry`s, `etc/tcb-baseline.txt`).

Two things are not covered by any proof:
- **Liveness.** This is what the PR trades: a removed leader no longer keeps the cluster led
  until an election.
- **The API break.** `Config.StepDownOnRemoval` disappears, so a caller that sets it no longer
  compiles. etcd's server never sets it; the register example here did.

## Applying the PR

- `raft.go` and `rafttest/interaction_env_handler_add_nodes.go` applied cleanly with `git
  apply -3` (the hunks do not touch messages, so there was no gogoproto/protobuf-go v2
  conflict). The testdata changes applied too.
- **Divergence, test only.** The fork's own regression test `readindex_singleton_test.go`
  (`TestReadIndexSingletonRemovedLeaderStale`, from the read-index fix) failed. It asserts that
  the removed leader is still leader, which was the old default. That scenario is now
  unreachable, so the test returns after checking that the node is a `StateFollower`. No
  non-test code differs from the PR.
- `go build ./...` and `go test ./...` pass in the fork worktree.

## Changed functions, types and fields

| Item | Kind | Before (lean) | After | Outcome |
|---|---|---|---|---|
| `raft.switchToConfig` | behavior change | verified | verified | new spec = old spec with the premise `s.sdr = true` (removed leader) dropped: weaker precondition, so compatible |
| `newRaft` | refactor (no longer copies the field) | verified | verified | old spec minus the post conjunct `s.sdr = cv.StepDownOnRemoval'` (the field no longer exists) |
| `Config.validate` | unchanged code; its spec named the field | verified | verified | post conjunct `cv'.StepDownOnRemoval' = cv.StepDownOnRemoval'` dropped |
| type `Config` | field `StepDownOnRemoval` removed | n/a | n/a | n/a |
| type `raft` | field `stepDownOnRemoval` removed | n/a | n/a | `ownRaftPhys`'s conjunct `rv.stepDownOnRemoval' = s.sdr` and `raftOwn`'s persistent points-to removed; `NState.sdr` removed |
| `rafttest.handleAddNodes` | test harness | not translated | not translated | not verified |

`etc/verified-code.py --functions --package go.etcd.io/raft/v3` reports the same before and
after: raft/v3 has 260 of 327 functions verified. All three changed functions are `verified
(sorry-free)`. On the branch the script counts lines against the pinned Go source, so its line
numbers are the pin's.

`switchToConfig`, old and new: `Spec/go_etcd_io/raft/v3/raft__switchToConfig.lean`
(`raft.switchToConfig.spec`).
- **Old:** a leader must either stay a voter of either half with `MatchKept`, or leave the voters
  with `s.sdr = true`, i.e. the `Config` asked for the step-down.
- **New:** a leader either stays a voter (`MatchKept`) or leaves the voters, with no further
  condition. The result is the same `SwitchOkC` (`∃ pvs, s' = { becomeFollower s1 s1.term 0 with
  prvals := pvs }` for the removed leader).
- **Proof change:** only the deleted load of `r.stepDownOnRemoval`
  (`Proof/go_etcd_io/raft/v3/raft__switchToConfig.lean`).
- **No `spec_implies_old` lemma:** the old statement names `NState.sdr` and the deleted field,
  so it cannot be stated against the new translation. The implication is syntactic: a premise
  conjunct is removed.

## Callers (step 6)

The spec change is compatible, but the shared state changed (a struct field and its invariant
went), so every user of the field or of `sdr` was rebuilt. The changes are all removals:

- `raft.applyConfChange`: premise `s.role = .leader → id ∉ c'.cfg.voters → s.sdr = true`
  removed. Re-proved.
- `RawNode.ApplyConfChange` (static and dynamic), `wp_applyConf_dyn` (`InvNodeRun.lean`):
  - the `sdrOk` invariant of `ownRawNode` (in the dynamic mode the field is on) is deleted;
  - `wp_applyConf_dyn` read it only to pass the premise above.
  - Re-proved. The other `RawNode`/`node` proofs that threaded `Hsdrf` were rebuilt with it removed.
- `RestartNode`: premise `md.isDyn = true → cv.StepDownOnRemoval' = true` removed. A dynamic
  `RestartNode` now accepts any `Config`, including etcd's (which never set the field).
  Re-proved.
- `NewRawNode`, `RawNode.Bootstrap`, `setupNode`, `StartNode`: `rawNodeFresh` lost its `sdr`
  parameter. Re-proved; `StartNode` is static only, as before.
- `raft.restore`: unaffected (a follower); rebuilt.
- The register example (`examples/register`), an application that set `StepDownOnRemoval: true`:
  - **Go side:** the field is removed from `cluster.go` and `register_test.go`, and `go.mod` is
    replaced to the local fork worktree. `go test` passes.
  - **Lean side:** re-translated; `Main.lean`'s `nodeConfig` and its `RestartNode` call lost the
    field and the premise.
  - **API break:** this is the user-visible break the PR announces. The register's contract does
    not change.
- etcd's server proofs (static mode; `bootstrappedRaft.newRaftNode` over `StartNode`): rebuilt
  unchanged.
- The protocol model `Protocol/StepR.lean`: its `stepDown` rule is unchanged (an optional rule
  the code-level `SwitchOkC` forces); only comments changed.

Stopped there. The exported entry points (`StartNode`, `RestartNode`, `NewRawNode`) are all
re-proved, and their only spec change is a removed premise, which the PR states (a breaking
change in its title and body).

## Trust base (step 7)

- `etc/tcb-report.py --check`, after a full `lake build` of the worktree: matches
  `etc/tcb-baseline.txt` (229 axioms, 12 `sorry`s).
- Collection `etc/tcb-collections/pr-raft-239.txt` (the changed functions, their callers above,
  the register): 13 axioms and 10 `sorry`s, the same on `lean`. The `sorry`s are the
  package-initialization ones: `crypto/rand`, `errors`, `raftpb`, `proto`, `log`, `math/big`,
  `math`, `os`, `strconv`, `time`. The comparison was checked with `--check` against the main
  checkout's `.lake/tcb.json`.
- No postulate or `sorry` was added.

## Findings

- **Bugs the PR introduces:** none found. The reviewer subagent found nothing blocking.
- **Behavior change, by design.** With the old default (false, which etcd's server uses), a
  removed leader stayed leader with no vote of its own, kept heartbeating, and could commit its
  last entries and drive the next change without an election. Under the PR the group has no
  leader for about one election timeout.
- **Leftovers on the removed leader, as in any step-down.** Its pending read-index requests go
  unanswered, its uncommitted proposals are dropped (the PR keeps the TODO), and it ignores the
  `MsgAppResp`s that arrive afterwards. It cannot campaign again (it is not promotable).
- **Joint configurations** (checked by the reviewer against `SwitchOkC`):
  - a leader only in the outgoing half stays leader until the leave-joint change applies;
  - a leader being demoted (outgoing ∩ `LearnersNext`) also stays until then;
  - an untracked leader or a learner steps down.
- **The PR fixes part of an existing issue.**
  - `issues/raft-readindex-singleton-stale.md`, execution 2: a removed leader answering a
    single-voter read index. It becomes unreachable, since the removed leader is a follower.
  - Execution 1 is not affected; the fork's fix stays needed.
  - The issue's front matter now links the PR.
- **Not affected:** `issues/raft-advance-before-applyconfchange.md` (a removed *candidate*
  stays a candidate). The candidate premise of `switchToConfig`/`applyConfChange` stays.
- **No bug found in the existing code.**
- **Premises that could now be relaxed** (not done here):
  - `RawNode.ApplyConfChange`'s static-mode `CCApplies` requires the node to stay a voter. For a
    leader the Go code no longer needs that, though the static fixed-voter ghost state still
    presumes it.
  - `StartNode` could be extended to the dynamic mode.
  - `StepR.stepDown` could be made mandatory in the model.

## Notes on this branch

- `Code/` and `GeneratedProof/` (raft and register) are translated from the unpushed fork
  commit `0a099f0cc` and from `examples/register` with a local `replace`. So `etc/goose.py
  --check` fails here, and the branch must not be merged into `lean`.
- When the PR merges and the pin moves past it, this branch's spec and proof changes are the
  starting point.

## Draft review comment (for the user to edit and post)

> I checked this change against a model of `switchToConfig` and its callers (`applyConfChange`,
> `RawNode.ApplyConfChange`, `NewRawNode`/`RestartNode`/`StartNode`). With the flag gone, a leader
> that is removed or demoted to a learner always becomes a follower at its current term, and
> nothing else in `switchToConfig` changes. Joint configurations behave as expected: a leader
> that is only in the outgoing half, or is being demoted via `LearnersNext`, stays leader until
> the joint configuration is left. The safety arguments that used to need
> `StepDownOnRemoval: true` now hold for every `Config`. Two things worth stating in the release
> notes: removing `Config.StepDownOnRemoval` breaks the build of callers that set it, and with the
> old default a removed leader kept leading (and could commit its tail and the next
> configuration change) until an election, which no longer happens, so a group whose leader
> removes itself now waits one election timeout for a new leader.

(Left out of the draft on purpose: the stale read by a removed leader through the single-voter
`ReadIndex` shortcut, which this PR makes unreachable, is in `issues/` with `upstream: none`.)
