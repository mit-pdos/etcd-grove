/-
`(*lessor).Lookup` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart); see
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

/-- `le.Lookup(id)` (read-locked): the lease map's lease of `id`, nil exactly when `id` is not
live (`L`, the live set the caller's share of `γl` names). -/
abbrev lease.lessor.Lookup.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (id : w64) (q : Qp) (L : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      lessorRd lp γl ∗ leaseFrag γl q L }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Lookup")) (Val #id))
  {{ (l : Loc), RET #l; lessorRd lp γl ∗ leaseFrag γl q L ∗ ⌜l = null ↔ id ∉ L⌝ ∗
      (⌜l = null⌝ ∨ isLeaseObj l) }}

end spec

end EtcdGrove
end Perennial
