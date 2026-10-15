/-
`(*lessor).GetLease` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart); see
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

/-- `le.GetLease(item)` (read-locked): the item map's lease of `item` (`NoLease` if none). -/
abbrev lease.lessor.GetLease.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (item : LeaseItem),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      lessorRd lp γl }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"GetLease")) (Val #item))
  {{ (id : w64), RET #id; lessorRd lp γl }}

end spec

end EtcdGrove
end Perennial
