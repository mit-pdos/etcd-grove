module
public import Proof.go_etcd_io.bbolt.internal.freelist.Model
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Read

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

/-- `t.Reload(p)`: `Read(p)`, then the free ids but the pending ones (none: the page's ids are
not pending) are reloaded (`NoSyncReload`). -/
abbrev shared.Reload.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (s : Loc) (σ : FLState) (p : Loc)
    (pv : go_etcd_io.bbolt.internal.common.Page) (dq : DFrac) (c : w64) (xs : List w64) (dq2 : DFrac),
  I.InitSpec → I.FreePageIdsSpec → p.locCar ≠ 0 → pv.flags' = W16 16 →
  (fpOverflow pv → 0 ≤ sint.Z c) →
  xs.Nodup → (∀ x ∈ xs, 2 ≤ uint.Z x ∧ x ∉ σ.pendingIds) → xs.length + σ.pendingCount < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ I.hdl s ∗ ownShared s I.iface σ ∗ I.own s σ.free ∗
      p ↦{dq} pv ∗ fpCountCell p pv dq c ∗ fpIdsSlice p pv c ↦*{dq2} xs }}
    (App (Val (s @!! go.GoType.PointerType shared.ty @!! go!"Reload")) (Val #p))
  {{ (free' : List w64), RET #(); ⌜PgidsIncr free' ∧ free'.Perm xs⌝ ∗
      ownShared s I.iface { σ with free := free' } ∗ I.own s free' ∗
      p ↦{dq} pv ∗ fpCountCell p pv dq c ∗ fpIdsSlice p pv c ↦*{dq2} xs }}

end spec

end bbolt
end EtcdGrove
end Perennial
