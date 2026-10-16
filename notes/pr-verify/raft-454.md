# etcd-io/raft#454: "raft: match exact storage errors in bootstrap test"

- PR: https://github.com/etcd-io/raft/pull/454, open, head `4e7ec16b82f369d37a258aadbcb35db2d7e24604`
  (two commits: `d6e469644` "raft: return error for rejected conf change", which is the whole of
  etcd-io/raft#453, "Fixes #354"; and `4e7ec16b8` "raft: match exact storage errors in bootstrap
  test"). The title and description cover only the second commit, which changes tests only.
- Verified at: fork branch `pr-raft-454-goose-lean` (`~/etcd-pr/raft-454`), commit `1ba458a05`,
  the PR's non-test diff (`3f4062b3c..4e7ec16b8`) applied onto the pinned `raft37-goose-lean`
  (`509271dac`). It applied cleanly (`raft.go`, `testdata/confchange_v2_add_single_explicit.txt`):
  no conflicts, no rewrites. The upstream commits between the fork's base `b867cf13f` and the PR's
  merge base `3f4062b3c` change no Go file. `go build ./...` and `go test .` pass with the PR's tests.
- This repository: branch `pr-verify/raft-454` (`/shared/etcd-grove-pr/raft-454`). `Code/` was
  regenerated from the fork worktree (`etc/goose.py --project raft --src raft=...`); the pin in
  `etc/goose.py` is unchanged, so `etc/goose.py --check` fails on this branch, as expected.

## Verdict

The code change is sound as far as raft's own guarantees go. After the PR, `stepLeader` returns
`ErrConfChangeRejected` exactly when the leader appended and broadcast a proposal in which it
refused (replaced by an empty normal entry) at least one conf change. That is proved
(`stepLeader.spec`, new binder `rej`). Nothing else changes: same log, messages and
`pendingConfIndex`, and every existing result rebuilds. No new axiom or `sorry`.

But the PR does not do what its linked issue (#354) asks for etcd. Three points:

1. **No effect through `Node`.** `Node.ProposeConfChange` does not wait for the step's result, so
   `node.run` throws the new error away. Only `RawNode` users (and direct `raft.Step` callers) on
   the leader ever see it.
2. **"Error" does not mean "not appended".** A batch that also held normal entries was appended,
   and so was the refused change's empty entry. A caller that treats any `Step` error as "not
   proposed" will retry or fail entries that will commit.
3. **The PR's title and description do not mention this API change.** They describe only a
   test-only change.

The test-only commit also does not do what it says. `require.Error(t, err, ErrCompacted)` passes
`ErrCompacted` as the failure message, not as the expected error, so the assertion is no stronger
than before. That needs `require.ErrorIs`.

## Changed functions

| Function (package `go.etcd.io/raft/v3`) | Kind | Before | After | Outcome |
|---|---|---|---|---|
| `stepLeader` (`raft.go`) | behavior change | verified | verified | new spec, incompatible (an error where `nil` was), callers checked |
| package initializer (`ErrConfChangeRejected` var) | new global | verified (`Init.lean`; other packages' inits `sorry` as before) | verified | `isInitialized` gains `ErrConfRej` |

No changed types or struct fields. The new package-level variable `ErrConfChangeRejected` is in
`isInitialized`, as `ErrConfRej` (`Proof/go_etcd_io/raft/v3/Base.lean`), with the initializer's
proof (`Init.lean`). It is placed last, so the positional patterns that unpack `isInitialized`
are unchanged.

### `stepLeader`: old and new spec

- Old (`lean`): a `MsgProp` returns `ErrProposalDropped` when dropped and `nil` otherwise
  (`LeaderStepResultC`/`LeaderProposeResult`).
- New (`Spec/go_etcd_io/raft/v3/stepLeader.lean`): the post has a flag `rej` with
  `LeaderStepResultCR`.
  - For a proposal that was not dropped, `rej = propConfRej applied lastIndex pci ents cs joint`:
    the loop's `rejectedConfChange` flag, a fold that is true iff some conf change of the batch is
    refused (pending, or `wantsLeaveJoint ≠ alreadyJoint`). It is computed over the same decoded
    changes `cs` as the appended batch (`Proof/go_etcd_io/raft/v3/CCModel.lean`, `propConfRej`
    and its lemmas).
  - The error is `if dropped then ErrProposalDropped else if rej then ErrConfChangeRejected else nil`.
  - `LeaderStepResultCR.old` gives back the old result, `.rej_nonprop` says no other message type
    sets the flag, and `.rej_conf` says the flag implies a conf-change entry in the batch.
  - The new spec does not imply the old one: the error differs.

## Callers (step 6)

`stepLeader` is called only by `raft.Step`; the error goes through `Step` unchanged.

- `raft.Step` (verified, spec changed). `Spec/go_etcd_io/raft/v3/raft__Step.lean`: its error
  gains a third disjunct, `⌜m.Type' = MsgProp ∧ ∃ e ∈ ents, IsConfEnt e⌝ ∗ ErrConfChangeRejected ↦□ err`.
  The 11 per-type branches that call `stepLeader` with other types rebuild with `rej = false`. The
  `MsgProp` branch (`raft__Step/MsgProp.lean`) carries the new error.
  - `RawNode.ProposeConfChange` (verified, exported API, spec changed): its error gains
    `ErrConfChangeRejected` (`Spec/.../RawNode__ProposeConfChange.lean`). This is a user-visible
    change that the PR's title, description and CHANGELOG do not mention (the PR adds the doc
    comment on the variable only).
  - `RawNode.Propose` (verified, spec unchanged): its single normal entry excludes the new
    disjunct.
  - `RawNode.Step` (verified, spec unchanged): its spec makes no claim on the error. In Go, a
    leader's `RawNode.Step` on a proposal forwarded by a follower can now return
    `ErrConfChangeRejected` to the leader's application, while the proposer gets nothing.
  - `RawNode.Campaign`, `ForgetLeader`, `ReportSnapshot`, `ReportUnreachable`, `TransferLeader`,
    `raft.tickElection`, `raft.tickHeartbeat`, `RawNode.Advance`, `RawNode.ReadIndex` (verified,
    specs unchanged): these step no proposal, and the new disjunct is refuted.
  - `node.run`, through `wp_rn_raft_Step_prop` (`InvNodeRun.lean`; verified, spec unchanged). The
    lemma's post is now `stepErr err ∨ ⌜a conf-change entry⌝`. In `run`, the only proposal with a
    result channel is `Propose`'s, of one normal entry, so the handoff still carries `stepErr`
    (`nil` or `ErrProposalDropped`). Forwarded proposals and `node.ProposeConfChange` have no
    result channel, and their error is dropped.
  - From there, `node.Propose`, `node.ProposeConfChange`, `propErr`, `stepErr` and the etcd
    server's proofs over them (`NodeBridge`, `InvRequest`) are unchanged. The paths stop here.
  - `raft.appliedTo`'s auto-leave proposal: the PR changes only which line it logs. The proposal
    is never refused at a leader (no pending change once applied ≥ `pendingConfIndex`, and
    `AutoLeave` means joint), and that case is out of scope of `appliedTo.spec` anyway.

Unchecked: none of raft's Go callers of `Step`. Outside raft, etcd uses only `Node`, which never
sees the new error.

## Trust base

No new axiom, no new `sorry` (`git diff lean -- Spec Proof` adds neither, and
`etc/tcb-report.py --check` matches `etc/tcb-baseline.txt` unchanged: 229 axioms, 12 `sorry`s).
The new collection `etc/tcb-collections/pr-raft-454.txt` holds the roots above (`stepLeader`,
`raft__Step`, `RawNode__ProposeConfChange`, `RawNode__Propose`, `RawNode__Step`, `node__run`,
`node__Propose`). They rest on no `sorry` and on 13 trust-boundary axioms, all of them already on
`lean`: `DescribeConfChange`, `context.ErrDone`, `fmt.Errorf`, protobuf's
`Clone{ConfState,Entry,Snapshot}`, `EqualConfState`, `MarshalConfChange(V2)`, `SizeEntry` and
`UnmarshalConfChange(V2)`, and `raftpb.ConfChangeType.String`. The new error's branch uses only
what the old code already used: the loop's `Unmarshal` axioms and `DescribeConfChange` for the
refusal's log line.

## Findings

These are about the PR, not the pinned code, so they are not in `issues/`. Reproductions:
`/tmp/claude-0/-shared-etcd-grove/6101526d-6539-4872-a190-a0b4b0fe455b/scratchpad/tests/pr454_test.go`,
run against the PR head (both pass, showing the behavior).

1. **Mixed batch** (`TestPR454MixedBatchRejectedButAppended`): a `MsgProp` with a normal entry and
   a conf change, at a leader with a change pending, returns `ErrConfChangeRejected`. The normal
   entry is appended, and so is an empty entry in place of the change. A later refused
   `RawNode.ProposeConfChange` returns the error, and the log still grows by one entry. This is
   the batching concern raised on #354.
2. **Node API** (`TestPR454NodeProposeConfChangeNoError`): `Node.ProposeConfChange` returns `nil`
   for a refused change, as before. The scenario of #354 (an application such as etcd that
   believes the change was accepted) is not fixed for `Node` users.
3. **Followers:** a change proposed at a follower is forwarded with `nil`. If the leader refuses
   it, the error surfaces in the leader's `RawNode.Step` for the incoming message, where its
   application cannot act on it.
4. **Test commit:** `require.Error(t, err, ErrCompacted)` and `require.Error(t, err, ErrUnavailable)`
   (`rawnode_test.go`) do not match the error; `require.ErrorIs` does. The `// TODO(tbg): match
   exact error` comment is left in place.

Reviewer's open points (a fresh reviewer read the diff, specs and proofs):
- `raft.Step.spec`'s new disjunct does not say that the batch was appended. Only `stepLeader`'s
  spec does. Strengthening `Step`'s error to carry "appended, with the refused changes emptied"
  would let a verified `RawNode` client rely on it. Left open.
- `cs` in `LeaderProposeResult(R)` is constrained only by `CCTypesOk`, not by what the bytes
  decode to (the existing design; a client cannot recover which change was refused).
- `isInitialized` records only `ErrConfChangeRejected ≠ nil`, not that it differs from
  `ErrProposalDropped`. Nothing compares the two.

## Draft review comment (for the user to edit and post)

> This PR includes the commit of #453 ("raft: return error for rejected conf change") in addition
> to the test change in the title. That is an API change: `Step`/`RawNode.ProposeConfChange` can
> now return `ErrConfChangeRejected`. Worth saying so in the title and description, and in the
> CHANGELOG.
>
> A few things about the behavior:
> - The error is returned after the batch was appended and broadcast. A `MsgProp` with several
>   entries (say a normal entry and a conf change that is refused because one is pending) gets
>   the error even though the normal entry, and an empty entry in place of the change, will
>   commit. Callers that read an error as "not proposed" (as with `ErrProposalDropped`) will
>   retry. The doc comment should say that the proposal was still appended, or the error should
>   only be returned when the batch held nothing else.
> - `Node.ProposeConfChange` doesn't wait for the result, so `Node` users (etcd included) never
>   see the new error. #354 stays as it was for them.
> - A conf change proposed at a follower is forwarded with `nil`. If the leader refuses it, the
>   error comes out of the leader's `RawNode.Step` for the forwarded message instead.
> - In `rawnode_test.go`, `require.Error(t, err, ErrCompacted)` treats `ErrCompacted` as the
>   failure message. `require.ErrorIs(t, err, ErrCompacted)` checks the error.
