/-
`(*lessor).Attach` (`server/lease/lessor.go`). Lean-first (no Rocq counterpart); see
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

/-- `le.Attach(id, items)` (locked): adds the items to the lease's item set and the item map;
for a live `id` (in the caller's live set `L`) it returns `nil` (else `ErrLeaseNotFound`). -/
abbrev lease.lessor.Attach.spec : Prop :=
  ∀ (lp : Loc) (γl : GName) (id : w64) (items : GoSlice) (xs : List LeaseItem) (dq : DFrac)
    (q : Qp) (L : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorInv lp γl ∗
      leaseFrag γl q L ∗ items ↦*{dq} xs }}
    (App (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"Attach")) (Val #id)) (Val #items))
  {{ (err : GoInterface), RET #err; leaseFrag γl q L ∗ items ↦*{dq} xs ∗
      ⌜id ∈ L → err = GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
