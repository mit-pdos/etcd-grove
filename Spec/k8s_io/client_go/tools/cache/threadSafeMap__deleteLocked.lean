/-
`(*threadSafeMap).deleteLocked(key)` (`thread_safe_store.go:355`): removes the key's object from
the indices and the items, under the write lock. Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.TSDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- `c.deleteLocked(key)` with the write lock's resources (the items' recorded index values `iv`):
the key not in the items, with new recorded values `iv'`, the store's invariant kept. -/
abbrev threadSafeMap.deleteLocked.spec : Prop :=
  ∀ (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (σ : St) (ph : Ph)
    (iv : IV) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      structFieldRef threadSafeMap go!"index" c ↦□ γ.idx ∗
      structFieldRef storeIndex go!"indexers" γ.idx ↦□ γ.im ∗
      tsPhys c γ σ ph 1 ∗ tsPers OK Fam σ ph iv ∗
      ⌜ixOk (σ.fns Fam) iv ph.ix ∧ ivWf (σ.fns Fam) σ.items iv⌝ }}
    (App (Val (c @!! go.GoType.PointerType threadSafeMap.ty @!! go!"deleteLocked")) (Val #key))
  {{ RET #(); ∃ (ix' : Ix) (iv' : IV),
      tsPhys c γ { σ with items := GMap.delete key σ.items } { ph with ix := ix' } 1 ∗
      tsPers OK Fam { σ with items := GMap.delete key σ.items } { ph with ix := ix' } iv' ∗
      ⌜ixOk (σ.fns Fam) iv' ix' ∧ ivWf (σ.fns Fam) (GMap.delete key σ.items) iv'⌝ }}

end spec

end cache
end EtcdGrove
end Perennial
