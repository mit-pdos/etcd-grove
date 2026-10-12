module
public import Proof.go_etcd_io.bbolt.internal.freelist.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `t.NoSyncReload(pgIds)`: the free ids become the increasing ids `pgIds` (at least 2) but the
pending ones (`Init`). `pgIds` may be borrowed from the implementation's own part, given back
before `Init` (the wand: for a caller's own slice, `Q` is the slice). -/
abbrev shared.NoSyncReload.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (s : Loc) (σ : FLState) (pg : GoSlice) (xs : List w64) (dq : DFrac)
    (Q : IProp GF),
  I.InitSpec → PgidsIncr xs → (∀ x ∈ xs, 2 ≤ uint.Z x) → xs.length + σ.pendingCount < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ I.hdl s ∗ ownShared s I.iface σ ∗ pg ↦*{dq} xs ∗
      (pg ↦*{dq} xs -∗ I.own s σ.free ∗ Q) }}
    (App (Val (s @!! go.GoType.PointerType shared.ty @!! go!"NoSyncReload")) (Val #pg))
  {{ RET #(); ownShared s I.iface { σ with free := xs.filter (fun x => decide (x ∉ σ.pendingIds)) } ∗
      I.own s (xs.filter (fun x => decide (x ∉ σ.pendingIds))) ∗ Q }}

end spec

end bbolt
end EtcdGrove
end Perennial
