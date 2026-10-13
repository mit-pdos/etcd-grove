/-
`confchange.toConfChangeSingle(cs)` turns a `ConfState` into the single changes that
rebuild it. Lean-first (no Rocq counterpart); see `InvConfchange.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvConfchange

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

/-- For a non-joint `ConfState` (empty `VotersOutgoing` and `LearnersNext`): no outgoing
changes (`out` stays `nil`) and one `AddNode id` per voter, then one `AddLearnerNode id` per
learner (since 2026-10-13; until then `Learners` was empty), in order, in a fresh slice. The
two empty slices are ranged over but never read, so they need no points-to. -/
abbrev confchange.toConfChangeSingle.spec : Prop :=
  ∀ (cs : raftpb.ConfState) (voters learners : List w64) (dq dql : DFrac),
  cs.VotersOutgoing'.len = W64 0 →
  cs.LearnersNext'.len = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ cs.Voters' ↦*{dq} voters ∗
      ownIdList cs.Learners' dql learners }}
    (App (Val #(functions confchange.toConfChangeSingle [])) (Val #cs))
  {{ (s : GoSlice), RET (PairV #slice.nil #s);
      cs.Voters' ↦*{dq} voters ∗ ownIdList cs.Learners' dql learners ∗
      s ↦* (voters.map addNodeCC ++ learners.map addLearnerCC) ∗
      ownSliceCap raftpb.ConfChangeSingle s (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
