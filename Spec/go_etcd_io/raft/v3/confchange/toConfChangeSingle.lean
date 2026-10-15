/-
`confchange.toConfChangeSingle(cs)` turns a `ConfState` into the single changes that
rebuild it. Lean-first (no Rocq counterpart); see `InvConfchange.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRestore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The changes `Restore` replays a `ConfState` as (`InvRestore.lean`): `out` holds one
`AddNode` per outgoing voter (`restoreOutCC`; `nil` when there is none), `in` one `RemoveNode`
per outgoing voter, then one `AddNode` per voter, one `AddLearnerNode` per learner and per
staged learner (`restoreInCC`), in a fresh slice. Generalized 2026-10-14 (reconfiguration
stage B8) from the non-joint case (empty `VotersOutgoing` and `LearnersNext`). The three id
lists other than the voters may come without a points-to when empty (`ownIdList`). -/
abbrev confchange.toConfChangeSingle.spec : Prop :=
  ∀ (cs : raftpb.ConfState) (voters learners outgoing learnersNext : List w64)
    (dq dql dqo dqn : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗
      cs.Voters' ↦*{dq} voters ∗ ownIdList cs.Learners' dql learners ∗
      ownIdList cs.VotersOutgoing' dqo outgoing ∗ ownIdList cs.LearnersNext' dqn learnersNext }}
    (App (Val #(functions confchange.toConfChangeSingle [])) (Val #cs))
  {{ (o s : GoSlice), RET (PairV #o #s);
      cs.Voters' ↦*{dq} voters ∗ ownIdList cs.Learners' dql learners ∗
      ownIdList cs.VotersOutgoing' dqo outgoing ∗ ownIdList cs.LearnersNext' dqn learnersNext ∗
      o ↦* restoreOutCC outgoing ∗
      s ↦* restoreInCC outgoing voters learners learnersNext ∗
      ownSliceCap raftpb.ConfChangeSingle s (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
