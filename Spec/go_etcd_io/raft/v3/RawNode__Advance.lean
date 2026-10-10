/-
Port of `election_proof/spec_RawNode__Advance.v` (857d09190), made client-facing on
2026-10-09.

Until 2026-10-09 the spec was stated on the node's states (`ownRawNode cfg rn id s rs`
at the `NState` `s`, `ownRaftGhost`, `NStateRel`, the `Step` it refines) and had two
protocol premises: `PstepCommitMono` (the protocol's commit index never moves back,
now the lemma `Step.commit_mono`, `Protocol/Facts.lean`) and `AdvanceOk s rs.steps` on
the queue at the current state (now `StepsOk`, part of `ownRawNode`, `InvRawnode.lean`).
Until 2026-10-10 it also required `rs.advanceable` (see the docstring) and kept the
term.

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

Steps the local messages the last `Ready` queued -- the node's own responses from
`msgsAfterAppend` (a candidate's vote for itself, a pre-candidate's pre-vote for itself,
a leader's acknowledgement of its own entries), the acknowledgement that the
application appended its entries (`MsgStorageAppendResp`, whose `stableTo` moves them
stable) and that it applied its committed entries (`MsgStorageApplyResp`,
`appliedTo`) -- through `Step`, and empties the queue. The `Ready` argument is unused.

Premises:
- the application appended the last `Ready`'s entries (`rs.unpersisted = []`, after
  `ownRawNode_persist`): the `MsgStorageAppendResp` then acknowledges persisted entries
  only (`StableOk`, `Step`'s premise; Rocq's `ready_stable_ok`) -- also after `MsgApp`s
  stepped since the `Ready` truncated the log below the acknowledged entry (2026-10-10:
  the storage agrees with the log up to it by Log Matching, `stableOk_of_stored`);
- the term does not wrap if it is raised (2026-10-10): stepping the node's own
  pre-vote response may win a pre-election, whose `campaign` increments the term
  (`Step`'s premise for a pre-candidate's `MsgPreVoteResp`).

The node after: the queue empty, and the term up by at most one -- by a won pre-vote;
once one is won the node is a candidate, which ignores the rest of the queue's
pre-vote responses, and the queue's other responses are its own of earlier terms
(`RespStep`, `Spec/raft__Step.lean`). The rest of the client-facing state is
unchanged.

Until 2026-10-10 the spec required `rs.advanceable`, which `Ready` returned and no
client could establish: the proof covered only a queue without the node's own
responses, for which `Step`'s spec asks facts nothing recorded (`Term ≠ 0`, no
entries, a non-rejecting `MsgAppResp`, a term bound). They are recorded now:
`ownRaftPhys` keeps them for `msgsAfterAppend` (`AAMsgOk`, `InvRaftPhys.lean`) and
`Ready` hands them to the queue (`pendingRel`, `StepsOk`, `InvRawnode.lean`). -/
abbrev RawNode.Advance.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rd : Ready),
  rs.unpersisted = [] →
  uint.Z rs.term + 1 < 2 ^ 64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Advance")) (Val #rd))
  {{ (t : w64), RET #();
      ownRawNode γ rn id { rs with steps := [], term := t } ∗
      ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.term + 1⌝ }}

end spec

end EtcdGrove
end Perennial
