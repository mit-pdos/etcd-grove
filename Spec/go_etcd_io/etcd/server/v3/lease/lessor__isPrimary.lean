/-
`(*lessor).isPrimary` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.isPrimary()`: whether `le.demotec` is not nil. -/
abbrev lease.lessor.isPrimary.spec : Prop :=
  ∀ (lp : Loc) (dc : GoChan) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗
      lF go!"demotec" lp ↦{dq} dc }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"isPrimary")) (Val #()))
  {{ RET #(decide (dc ≠ chan.nil)); lF go!"demotec" lp ↦{dq} dc }}

end spec

end EtcdGrove
end Perennial
