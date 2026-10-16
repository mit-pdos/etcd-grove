# etcd-io/raft#43: stepWait not used in ProposeConfChange

<https://github.com/etcd-io/raft/issues/43>. Open, filed 2023-04-11, no labels, no fix. The
code is unchanged at the raft pin `509271dac`.

**The report.** `node.Propose` (`node.go:470-472` at the pin) goes through `stepWait`, so
`run` returns the proposal's own error (`ErrProposalDropped`, for
example: a leader transfer in progress, a full uncommitted budget, `DisableProposalForwarding`).
`node.ProposeConfChange` (`node.go:496-502`) goes through `n.Step` → `step` →
`stepWithWaitOption(ctx, m, false)` instead. It returns `nil` as soon as `run` takes the
message from `propc`, so a dropped conf change is never reported. One consequence: etcd's
`ExampleCluster_memberAddAsLearner` timed out, because etcd's `configure` waited out its
deadline. A commenter asks for a documented fail-fast contract for both `Propose` and
`ProposeConfChange`.

## Classification

**N** (documented behavior, really a request for a feature or a consistency change).
Secondary: **C-err**. The decisive fact: `Node.ProposeConfChange`'s comment (`node.go:141-145`)
says "the configuration change may be dropped with or without an error being returned". The
proved spec `node.ProposeConfChange.spec` states the error exactly: `nodeErr cd err`, that is
`nil`, `ErrStopped` or the context's error. That excludes `ErrProposalDropped` and allows `nil`
for a dropped change. `node.Propose.spec`, by contrast, has `propErr` (`nodeErr ∨ stepErr`). So
the spec records the asymmetry the reporter observed. It is the "precise outcome" gap of
raft#354, one level up.

## The code path and its verification state

Source: `/shared/etcd-grove-triage/coord/verified.txt`. All are "verified (sorry-free)".

| Go function | Spec |
|---|---|
| `node.ProposeConfChange` (`node.go:496`) | `Spec/go_etcd_io/raft/v3/node__ProposeConfChange.lean:40-50` (linked `Link.lean:1618`) |
| `node.Step` / `node.step` | `node__Step.lean`, `node__step.lean` |
| `node.stepWithWaitOption` (`node.go:514`) | `node__stepWithWaitOption.lean:53-61` |
| `node.stepWait` (`node.go:508`, used only by `Propose`) | `node__stepWait.lean` |
| `node.run` (steps it via `RawNode.ProposeConfChange` → `stepLeader`) | `node__run.lean`, `stepLeader.lean:150-159` |

## The argument (step 4)

1. **Observed.** `ProposeConfChange` returns `nil`, and the change is never appended. Either
   `run`'s `r.Step` returned `ErrProposalDropped`, which it discards when `pm.result` is `nil`
   (`node.go:386-393`), or the leader replaced the change with an empty entry. If no leader is
   known, `run` does not read `propc` at all (`propc = nil`, `node.go:376`), so both methods
   block until the context is done.
2. **Premises.** `CCAllowed γ.raft o` (`RawNode__ProposeConfChange.lean:79`) and `nodeCtx`. A
   real caller meets both. They have no bearing on the error.
3. **Postcondition.** `node__ProposeConfChange.lean:50`:
   `RET #err; ownCCI c dq (some o) ∗ nodeErr cd err`, where `nodeErr cd err := ⌜err = nil⌝ ∨
   errStopped err ∨ ctxErr cd err` (`Proof/go_etcd_io/raft/v3/InvNodeCtx.lean:174-176`). `nil`
   is allowed whatever `run` did with the proposal. The `stepWithWaitOption` spec gives
   `nodeErr` for `wait = false` and `propErr` for `wait = true` (`:61`), which is the exact
   asymmetry. The spec allows the outcome. It even rules out the "expected" `ErrProposalDropped`
   at the pin. If the issue's change (`stepWait`) were made, the spec would have to change to
   `propErr`, and proving that would be routine, since `Propose`'s path already does it.
4. Not X. Not a gap that lets an unintended behavior through, because the documentation allows
   it. As a request for a precise outcome, the gap is C-err.

The commenter's point that a leader-side drop is invisible also holds with `stepWait`: a
refused conf change is appended as an empty entry and `nil` is returned (raft#354's report,
`propConfStep`, `Proof/go_etcd_io/raft/v3/CCModel.lean:108-115`).

## Proposal (step 6)

**`confchange-propose-outcome`** (existing slug, from raft#354). Carry `run`'s step result and
`stepLeader`'s accept/refuse outcome to `node.ProposeConfChange.spec`. The addition from this
bug is the fail-fast half. With `stepWait`, the postcondition becomes `propErr cd err`, with
`stepErr err` meaning "dropped by `r.Step` (a leader transfer, the uncommitted budget, forwarding disabled)", and `err = nil` meaning
"stepped at a leader", refused or appended as raft#354's sketch says. Cost: small (the
`Propose` path is the model). It is useful for a future spec of etcd's `configure`.

## Files

None besides this report. There is no `issues/` file, since the behavior is documented
(`node.go:141-145`).
