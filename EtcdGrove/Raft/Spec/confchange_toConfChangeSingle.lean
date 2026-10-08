/-
`confchange.toConfChangeSingle(cs)` turns a `ConfState` into the single changes that
rebuild it. Lean-first (no Rocq counterpart); see `InvConfchange.lean`.
-/
import EtcdGrove.Raft.InvConfchange

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

/-- For a voters-only `ConfState` (empty `VotersOutgoing`, `Learners`,
`LearnersNext`): no outgoing changes (`out` stays `nil`) and one `AddNode id` per
voter, in order, in a fresh slice. The three empty slices are ranged over but never
read, so they need no points-to. -/
abbrev confchange.toConfChangeSingle.spec : Prop :=
  ∀ (cs : raftpb.ConfState) (voters : List w64) (dq : DFrac),
  cs.VotersOutgoing'.len = W64 0 →
  cs.Learners'.len = W64 0 →
  cs.LearnersNext'.len = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ cs.Voters' ↦*{dq} voters }}
    (App (Val #(functions confchange.toConfChangeSingle [])) (Val #cs))
  {{ (s : GoSlice), RET (PairV #slice.nil #s);
      cs.Voters' ↦*{dq} voters ∗ s ↦* voters.map addNodeCC ∗
      ownSliceCap raftpb.ConfChangeSingle s (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
