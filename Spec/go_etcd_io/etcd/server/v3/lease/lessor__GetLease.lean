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

/-- `le.GetLease(item)` (read-locked): the item map's lease of `item` (`NoLease` if none), the
lease owner's item map `I`'s (unit T3, L2b). -/
abbrev lease.lessor.GetLease.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (item : LeaseItem) (L : List w64) (I : GMap LeaseItem w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      lessorRd lp γl ∗ leaseOwn γl L I }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"GetLease")) (Val #item))
  {{ RET #((I.lookup item).getD (W64 0)); lessorRd lp γl ∗ leaseOwn γl L I }}

end spec

end EtcdGrove
end Perennial
