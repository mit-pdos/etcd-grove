module
public import Proof.go_etcd_io.bbolt.internal.freelist.Model
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Read
public import Proof.go_etcd_io.bbolt.internal.freelist.WeakState

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

/-- `t.Reload(p)`: `Read(p)`, then the free ids but the pending ones are reloaded
(`NoSyncReload`): the free ids become the ids of the freelist page `p` that are not pending,
sorted. The page may hold pending ids (bbolt writes the free and the pending ids into it, and
`Commit`'s rollback reloads it while an older transaction's pending entry survives); the state
before need only be weakly well-formed, the one after is well-formed. An empty page needs the
old free ids all pending (`hashMap.Init` of no ids keeps the old cache). -/
abbrev shared.Reload.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (s : Loc) (σ : FLState) (p : Loc)
    (pv : go_etcd_io.bbolt.internal.common.Page) (dq : DFrac) (c : w64) (xs : List w64) (dq2 : DFrac),
  I.InitSpecW → I.FreePageIdsSpec → p.locCar ≠ 0 → pv.flags' = W16 16 →
  (fpOverflow pv → 0 ≤ sint.Z c) →
  xs.Nodup → (∀ x ∈ xs, 2 ≤ uint.Z x) → xs.length + σ.pendingCount < 2 ^ 63 →
  (xs ≠ [] ∨ ∀ x ∈ σ.free, x ∈ σ.pendingIds) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ I.hdl s ∗ ownSharedW s I.iface σ ∗ I.own s σ.free ∗
      p ↦{dq} pv ∗ fpCountCell p pv dq c ∗ fpIdsSlice p pv c ↦*{dq2} xs }}
    (App (Val (s @!! go.GoType.PointerType shared.ty @!! go!"Reload")) (Val #p))
  {{ (free' : List w64), RET #();
      ⌜PgidsIncr free' ∧ free'.Perm (xs.filter (fun x => decide (x ∉ σ.pendingIds)))⌝ ∗
      ownShared s I.iface { σ with free := free' } ∗ I.own s free' ∗
      p ↦{dq} pv ∗ fpCountCell p pv dq c ∗ fpIdsSlice p pv c ↦*{dq2} xs }}

end spec

end bbolt
end EtcdGrove
end Perennial
