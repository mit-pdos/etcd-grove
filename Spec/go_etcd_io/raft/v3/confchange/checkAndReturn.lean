/-
`confchange.checkAndReturn(cfg, trk)` is `checkInvariants` returning its arguments.
Lean-first (no Rocq counterpart); see `InvConfchange.lean`.
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

/-- `checkAndReturn` on a config `checkInvariants` accepts returns it, with `nil`. -/
abbrev confchange.checkAndReturn.spec : Prop :=
  ∀ (cfg : tracker.Config) (trk v : Loc) (vm : GMap w64 Unit) (prs : GMap w64 Loc)
    (dqv dqp : DFrac),
  ConfigSimple cfg v →
  domSet prs = domSet vm →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ v ↦${dqv} vm ∗ trk ↦${dqp} prs }}
    (App (App (Val #(functions confchange.checkAndReturn [])) (Val #cfg)) (Val #trk))
  {{ RET (PairV (PairV #cfg #trk) #interface.nil); v ↦${dqv} vm ∗ trk ↦${dqp} prs }}

end spec

end EtcdGrove
end Perennial
