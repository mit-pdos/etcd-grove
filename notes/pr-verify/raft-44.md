# Verifying etcd-io/raft#44

- **PR**: etcd-io/raft#44, "raft: error on ignored proposal and wait for EntryConfChange
  results" (https://github.com/etcd-io/raft/pull/44), head `551232a5a2dd4ecbf36489baf177bffc43485cfb`,
  open, fixes etcd-io/raft#43 (`stepWait` not used in `ProposeConfChange`). Related:
  etcd-io/raft#354 (a refused conf change is silently turned into a no-op).
- **Verified at**: fork `upamanyus/etcd`, branch `pr-raft-44-goose-lean`, commit `c87ad2502`
  (not pushed), on top of the pinned raft `509271dac` (`raft37-goose-lean`, raft v3.7.0 plus the
  read-index fix). This repository: branch `pr-verify/raft-44`.

## Verdict

The PR does what it says for a proposal stepped at the leader. A conf change the leader
refuses is no longer appended as an empty entry. `Step` returns `ErrProposalDropped`, and
`Node.ProposeConfChange` now returns that error because it waits for the result. Both
functions are proved against specs that state this, with no new axiom or `sorry`. The proofs of
`raft.Step`, the node loop and the register example go through unchanged above them.

The early `return` has side effects that make the change unsafe to merge as it is:

1. `pendingConfIndex` is not rolled back. Take a batch whose earlier conf change was accepted
   and whose later one is refused. The batch is dropped, but `pendingConfIndex` already points
   past the last index. After that, every conf change is refused until some unrelated entry is
   appended at that index and applied. On an idle leader this can last forever, and it covers
   leaving a joint configuration too.
2. The whole batch is dropped, normal entries included. When the batch came from a follower,
   the follower's `Step` has already returned `nil`.
3. The PR at its head fails two of raft's own tests.

A follower still gets `nil` for a conf change the leader refuses. So for etcd, issue #43 is
fixed only on the leader.

**Not covered.** The specs do not tie `ErrProposalDropped` to the refusal at the
`Node`/`RawNode` layer: `nil` and the error are both allowed there, as before. The PR's
property is stated at `stepLeader`.

## Applying the PR

- `node.go`: applied cleanly.
- `raft.go`: one conflict, in the conf-change loop. The base has v3.7's `failedCheck`,
  `!r.disableConfChangeValidation`, `DescribeConfChange(cc)` and `r.trk.Config`. Resolution: keep
  the base's lines and replace its `m.GetEntries()[i] = &pb.Entry{Type: pb.EntryNormal.Enum()}`
  with the PR's `return ErrProposalDropped`. No behavior differs from the PR.
- Tests (the commit's only divergence from the PR):
  - `TestStepIgnoreConfig`: rewritten in the base's protobuf-go style.
  - Two tests that fail at the PR's own head (`notes/pr-verify/raft-44/prhead-own-tests.log`)
    are updated to the new behavior:
    - `TestRawNodeProposeAddDuplicateNode`: the refused duplicate now takes no index and returns
      `ErrProposalDropped`.
    - `testdata/confchange_v2_add_single_explicit.txt`: regenerated with `-rewrite`; the refused
      changes print `raft proposal dropped` and add no empty entry.
- `go build ./...` and `go test ./...` pass on the fork branch.
- `etc/goose.py --project raft --src raft=~/etcd-pr/raft-44` changes two functions in
  `Code/go_etcd_io/raft/v3.lean`: `node.ProposeConfChange` and `stepLeader`. The pin in
  `etc/goose.py` is unchanged, so `--check` fails on this branch by design.

## Changed functions

| Function | Kind | Before (on `lean`) | After | Outcome |
|---|---|---|---|---|
| `stepLeader` (raft.go, `MsgProp`) | behavior change | verified | verified | new spec, incompatible in the dropped case; caller `raft.Step` re-checked, its spec unchanged |
| `(*node).ProposeConfChange` (node.go) | behavior change | verified | verified | new spec (error `propErr` instead of `nodeErr`): a weaker postcondition, so incompatible; its one caller re-checked, spec unchanged |

No types, struct fields or package variables change. The node's `propc` protocol carries a new
kind of message (a conf change proposal with a result channel). Its invariant changed, and the
functions on that channel were re-checked as callers (below).

### `stepLeader`

`Spec/go_etcd_io/raft/v3/stepLeader.lean`, `LeaderProposeResult`. The proof is in
`Proof/go_etcd_io/raft/v3/stepLeader/MsgProp.lean`.

- **Old:**
  - Not dropped: the loop's batch is appended, with each refused conf change replaced by an
    empty entry (`PropRepl`).
  - Dropped: either nothing changed, or only `pendingConfIndex` moved, as the loop over the
    whole batch left it.
- **New:**
  - Not dropped: no conf change was refused, so the batch appended is the proposal itself
    (`(leaderPropConf s ents cs joint).1 = ents`).
  - Dropped: either nothing changed, or `pendingConfIndex` is as the loop over a prefix
    `ents.take k` left it. `k` is the batch's length when `appendEntry` refused it, and the
    refused entry's position when the loop returned early.
- **Proof:** the loop invariant gains "the loop's batch so far is `ents.take n`" (`Htk`). Each
  of the five refusal paths ends in `return ErrProposalDropped` (two for `ConfChange`, three for
  `ConfChangeV2`).
- **Why incompatible:** the dropped case is weaker (a prefix's `pendingConfIndex`).
- **Caller `raft.Step`** (`Proof/go_etcd_io/raft/v3/raft__Step/MsgProp.lean`): its spec is
  unchanged. The dynamic model's stuttering step `StepR.propDrop` takes any batch, so it is given
  the prefix. The new lemma it needs is `cctypes_take` (`Proof/go_etcd_io/raft/v3/CCModel.lean`).

### `node.ProposeConfChange`

`Spec/go_etcd_io/raft/v3/node__ProposeConfChange.lean`. The proof is in
`Proof/go_etcd_io/raft/v3/node__ProposeConfChange.lean`.

- **Old:** the error is `nodeErr`: `nil`, `ErrStopped` or the context's error. The proposal's
  result never reached the caller.
- **New:** the error is `propErr`, which is `nodeErr` or the proposal's result from `run`
  (`stepErr`: `nil` or `ErrProposalDropped`). The precondition is unchanged.

## Callers and shared state re-checked

- `stepLeader` → `raft.Step`: re-proved, spec unchanged, so the path stops there. Above it,
  `RawNode.Step`, `RawNode.ProposeConfChange` and the node loop rebuilt unchanged.
- `node.ProposeConfChange` → `Register.RemoveMember` (the register example): rebuilt, spec
  unchanged (it ignores the error). etcd's server `configure()` (`server/etcdserver/server.go`)
  is not translated. It returns the error as is, so a refused `MemberAdd`/`Remove`/`Update`
  now fails at once with `raft proposal dropped` (gRPC `Unknown`) instead of timing out. That
  is a user-visible change, and it applies only when the request is handled on the leader.
- The `propc` invariant (`propP`, `Proof/go_etcd_io/raft/v3/InvNode.lean`) gains a third
  disjunct: a proposal message (`fwdP`) with a result handoff. The functions on that channel,
  all re-proved, specs unchanged except as noted:
  - `node.run` (`node__run.lean`): new case. It steps the message as a forwarded one, then
    sends and closes the result.
  - `node.stepWithWaitOption`: `stepArg` gains `wait = true ∗ fwdP`; new case in the proof.
  - `node.stepWait`: its precondition is now the propose message or `fwdP`.
  - `node.Propose`: proof adjusted (`ileft`).
  - `node.step`: disjunct index adjusted.
  - `StartNode` and `RestartNode` allocate the handshake; they rebuilt unchanged.
- Built: `Proof.go_etcd_io.raft.v3.{Link,Results,SpecResults}`,
  `Proof.github_com.mit_pdos.etcd_grove.examples.register.{Link,Results}` and
  `Proof.go_etcd_io.etcd.server.v3.etcdserver.Link`.

## Trust base

- No new axiom, postulate or `sorry`.
- `#print axioms` of `wp_stepLeader`, `node.wp_ProposeConfChange`, `node.wp_stepWait` and
  `RawNode.wp_ProposeConfChange` is identical on `lean` and on this branch: the same
  trust-boundary axioms (`DescribeConfChange`, `proto.*`, `fmt.Errorf`, `context.ErrDone`, ...),
  no `sorryAx`.
- `etc/tcb-report.py` and `etc/verified-code.py` were not run: they need a full `lake build`
  of the branch, and only the affected modules were rebuilt.
- `etc/tcb-collections/pr-raft-44.txt` lists the roots, with no baseline yet.

## Findings

1. **A refused conf change in a batch leaves `pendingConfIndex` dangling (PR bug).**
   - Before returning, the loop has already set `pendingConfIndex = lastIndex + i + 1` for an
     earlier accepted conf change of the same batch. Nothing is appended.
   - From then on, every conf change is refused (`pendingConfIndex > applied`) until an
     unrelated entry is appended at that index and applied. On an idle leader that may never
     happen, and the PR's change means the retries no longer fill the index themselves.
   - Tests:
     - `notes/pr-verify/raft-44/batch_confchange_test.go`, at the PR head:
       `batch-prhead.log`.
     - `pending_conf_index_test.go`, `TestStepRefusedConfChangeInBatch`, on the fork: `pr.log`.
     - The reviewer's `review_raft44_test.go`, `TestReviewJointLeaveStallsAfterRefusedBatch`
       (`review-pr.log`; it passes at the base, `review-base.log`): a joint configuration
       cannot then be left.
   - The spec allows this: it is the dropped case with `k > 0`. It is a liveness problem, and
     safety is unaffected.
   - Fix: compute the new `pendingConfIndex` in a local variable and store it only after
     `appendEntry` accepts the batch.
2. **The same dangling index already exists in the pinned code (bug in existing code,
   recorded in `issues/raft-pendingconfindex-dangling-after-drop.md`).**
   - A conf change accepted by the loop but dropped by `appendEntry`'s uncommitted-size limit
     leaves `pendingConfIndex` past the last index.
   - At the base, the next conf change is then silently turned into an empty entry, which fills
     the index. With the PR it is dropped, so the leader keeps refusing.
   - Test: `TestConfChangeDroppedBySizeLeavesPendingConfIndex` (`base.log` vs `pr.log`). The
     fix above covers both cases.
3. **A whole batch is dropped, normal entries included (behavior change, not documented).**
   - Before, only the refused entry became an empty entry.
   - For a batch forwarded by a follower, the follower's `Step` already returned `nil`, so its
     normal entries are lost without notice. Test: `TestReviewForwardedBatchNormalEntryLost`.
   - This matches how `appendEntry`'s size limit already drops a batch, and raft's API allows
     dropping proposals without notice. Still, the PR's description does not mention it.
4. **The error reaches only proposals stepped at the leader (scope).** A follower forwards the
   proposal, and `stepFollower` returns `nil`. So `Node.ProposeConfChange` on a follower still
   returns `nil` for a change the leader refuses, and etcd's `configure()` there still waits
   until its timeout. Issue #43 is fixed on the leader only.
5. **The PR's own tests fail at its head.** `TestRawNodeProposeAddDuplicateNode` and
   `TestInteraction/confchange_v2_add_single_explicit` still expect the empty entry
   (`prhead-own-tests.log`). The fork commit updates both.
6. **The reviewer's other conclusions:**
   - Checked and found nothing:
     - `ProposeConfChange` waiting on `stepWait` cannot deadlock: `run` answers on a
       one-slot buffered channel right after `Step`.
     - A context cancelled after the handoff leaks nothing (`run` still sends into the buffer).
     - The auto-leave in `appliedTo` is never refused by the check itself.
     - `DisableConfChangeValidation` is unaffected.
     - The new `propP` disjunct is sound: `run` meets the producer obligation on both orders of
       the caller's `select`.
   - Open spec weaknesses, sound but weaker than they could be:
     - The dropped case does not say that entry `k` was a refused conf change.
     - The node-level error is not tied to the refusal.

All tests and logs are in `notes/pr-verify/raft-44/`, listed with revisions and commands in its
`README.md`.

## Draft review comment

> Thanks for this — returning an error for a refused conf change instead of silently appending
> an empty entry is a clear improvement for callers on the leader, and `ProposeConfChange`
> waiting like `Propose` does makes that error visible through `Node`.
>
> One problem with the early `return`: by the time a conf change at index `i` of the batch is
> refused, the loop may already have set `r.pendingConfIndex` for an earlier conf change in the
> same `MsgProp`. The batch is then dropped but `pendingConfIndex` is left pointing past
> `lastIndex()`, and every following conf change is refused (`pendingConfIndex > applied`) until
> some other entry gets appended at that index and applied — on an idle leader, indefinitely,
> including the proposal that leaves a joint config. Before this PR the refused entry was
> appended as an empty entry, which filled that index. A test: step `MsgProp` with two
> `EntryConfChange` entries on a leader with nothing pending; it returns `ErrProposalDropped`,
> `lastIndex()` is unchanged, `pendingConfIndex == lastIndex()+1`, and a following single conf
> change is dropped too. (The same dangling index already happens on `main` when `appendEntry`
> drops an accepted conf change for the uncommitted-size limit.) Computing the new
> `pendingConfIndex` in a local and storing it only after `appendEntry` succeeds would fix both.
>
> Two smaller points: the whole batch is now dropped, normal entries included — for a batch
> forwarded from a follower, whose `Step` already returned nil, those entries are lost without
> notice; worth a line in the description or doc comment. And on a follower,
> `ProposeConfChange` still returns nil for a change the leader refuses, so #43 is fixed only
> when the proposal is made on the leader. Also, `TestRawNodeProposeAddDuplicateNode` and
> `testdata/confchange_v2_add_single_explicit.txt` need updating for the new behavior.
