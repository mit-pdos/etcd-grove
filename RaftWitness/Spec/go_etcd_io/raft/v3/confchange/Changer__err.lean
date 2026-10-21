/-
`Changer.err(err)` returns zero values and the error. Lean-first (no Rocq counterpart);
see `InvConfchange.lean`.
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

/-- `err(e)` returns `(Config{}, nil, e)`. -/
abbrev confchange.Changer.err.spec : Prop :=
  ∀ (p : Loc) (chg : confchange.Changer) (err : GoInterface) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg }}
    (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"err")) (Val #err))
  {{ (cfg : tracker.Config), RET (PairV (PairV #cfg #(map.nil : GoMap)) #err); p ↦{dq} chg }}

end spec

end EtcdGrove
end Perennial
