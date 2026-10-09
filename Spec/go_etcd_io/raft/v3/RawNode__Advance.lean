/-
Port of `election_proof/spec_RawNode__Advance.v` (857d09190), made client-facing on
2026-10-09.

Until 2026-10-09 the spec was stated on the node's states (`ownRawNode cfg rn id s rs`
at the `NState` `s`, `ownRaftGhost`, `NStateRel`, the `Step` it refines) and had two
protocol premises: `PstepCommitMono` (the protocol's commit index never moves back,
now the lemma `Step.commit_mono`, `Protocol/Facts.lean`) and `AdvanceOk s rs.steps` on
the queue at the current state (now `StepsOk`, part of `ownRawNode` for an
`advanceable` queue, `InvRawnode.lean`).

Lean notes: As for `raft.Step.spec`, the section fixes `hlc := HasLC.hasLC` and has
`[AllG GF]`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [AllG GF]

/-- `rn.Advance(rd)` (`rawnode.go:482`):

    if rn.asyncStorageWrites { Panicf(...) }
    for i, m := range rn.stepsOnAdvance {
        _ = rn.raft.Step(m)
        rn.stepsOnAdvance[i] = pb.Message{}
    }
    rn.stepsOnAdvance = rn.stepsOnAdvance[:0]

Steps the local messages the last `Ready` queued -- the acknowledgement that the
application appended its entries (`MsgStorageAppendResp`, whose `stableTo` moves them
stable) and that it applied its committed entries (`MsgStorageApplyResp`,
`appliedTo`) -- through `Step`, and empties the queue. The client-facing state is
otherwise unchanged. The `Ready` argument is unused.

Premises:
- the application appended the last `Ready`'s entries (`rs.unpersisted = []`, after
  `ownRawNode_persist`): the `MsgStorageAppendResp` then acknowledges persisted entries
  only (`StableOk`, `Step`'s premise; Rocq's `ready_stable_ok`);
- **`rs.advanceable`: a gap, to be closed.** The proof covers only a queue without
  self-addressed responses (`Pending.self`: a candidate's own vote, a leader's own
  `MsgAppResp`, which `readyWithoutAccept` keeps from `msgsAfterAppend` for `Advance`
  to step). `Step`'s spec asks of each message facts the raft struct does not record for
  the queue -- its `Entries`' capacity, `Term ≠ 0`, a non-rejecting self `MsgAppResp`
  -- and, for a `MsgPreVoteResp`, a term bound at the state the earlier steps left,
  which `Step`'s postcondition does not describe beyond the protocol state (see
  notes/raft-replication-model.md, "Phase 4", for the fix). `Ready` returns
  `advanceable` (`true` exactly when it queued no such message, which its
  postcondition does not state: whether `msgsAfterAppend` holds one is protocol
  state -- a candidate's, or a leader's with new entries). So no client can establish
  this premise: until the gap is closed, a client calls `Ready` once and then neither
  `Advance` (unproved) nor `Ready` (which needs an empty queue). -/
abbrev RawNode.Advance.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rd : Ready),
  rs.advanceable = true →
  rs.unpersisted = [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Advance")) (Val #rd))
  {{ RET #(); ownRawNode γ rn id { rs with steps := [] } }}

end spec

end EtcdGrove
end Perennial
