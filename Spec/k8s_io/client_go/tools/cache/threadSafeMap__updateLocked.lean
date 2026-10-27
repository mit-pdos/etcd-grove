/-
`(*threadSafeMap).updateLocked(key, obj)` (`thread_safe_store.go:326`): stores the object and
moves it in the indices, under the write lock. Lean-first.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- `c.updateLocked(key, obj)` with the write lock's resources (the items' recorded index values
`iv`): the items have `obj` at `key`, with new recorded values `iv'`, the store's invariant kept. -/
abbrev threadSafeMap.updateLocked.spec : Prop :=
  ∀ (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (σ : St) (ph : Ph)
    (iv : IV) (key : GoString) (obj : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      structFieldRef threadSafeMap go!"index" c ↦□ γ.idx ∗
      structFieldRef storeIndex go!"indexers" γ.idx ↦□ γ.im ∗
      tsPhys c γ σ ph 1 ∗ tsPers OK Fam σ ph iv ∗ okNil OK obj ∗
      ⌜ixOk (σ.fns Fam) iv ph.ix ∧ ivWf (σ.fns Fam) σ.items iv⌝ }}
    (App (App (Val (c @!! go.GoType.PointerType threadSafeMap.ty @!! go!"updateLocked"))
      (Val #key)) (Val #obj))
  {{ RET #(); ∃ (ix' : Ix) (iv' : IV),
      tsPhys c γ { σ with items := <[key := obj]> σ.items } { ph with ix := ix' } 1 ∗
      tsPers OK Fam { σ with items := <[key := obj]> σ.items } { ph with ix := ix' } iv' ∗
      ⌜ixOk (σ.fns Fam) iv' ix' ∧ ivWf (σ.fns Fam) (<[key := obj]> σ.items) iv'⌝ }}

end spec

end cache
end EtcdGrove
end Perennial
