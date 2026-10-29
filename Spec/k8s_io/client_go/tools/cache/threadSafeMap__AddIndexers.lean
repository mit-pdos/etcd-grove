/-
`(*threadSafeMap).AddIndexers(newIndexers)` (`thread_safe_store.go:505`): adds indexers, indexing
the items already stored. Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.TSDefs
public import Spec.k8s_io.client_go.tools.cache.storeIndex__addIndexers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

open Classical in
/-- `AddIndexers` of the indexers `nids` (named by index into the client's family, as `fnIds`):
unchanged if a name is taken, otherwise the new indexers added. -/
def St.addIx [GooseExts] (σ : St) (nids : GMap GoString Nat) : St :=
  if nameClash σ.fnIds nids then σ else { σ with fnIds := nids ∪ σ.fnIds }

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **`c.AddIndexers(nm)`**, logically atomic (a writer), for a map `nm` of new indexers (read
only; at most `2^62`, the bound of `sets.List`'s sort) whose functions meet their contracts for
`Fam` at `nids`: the state `σ.addIx nids`, and an error exactly when a new name is already an
indexer's (`nameClash`). The items already stored are indexed by the new indexers (the store's
invariant, `ixOk`, holds of the new indexers). -/
abbrev threadSafeMap.AddIndexers.spec : Prop :=
  ∀ (c : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF) (nm : Loc)
    (dn : DFrac) (nfv : GMap GoString GoFunc) (nids : GMap GoString Nat),
  GMap.size nfv ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isTS c γ OK Fam ∗
      nm ↦${dn} nfv ∗ fnsOk OK nfv (GMap.fmap Fam nids) }}
  <<{ ∀∀ σ, storeSt γ σ }>>
    (App (Val (c @!! go.GoType.PointerType threadSafeMap.ty @!! go!"AddIndexers")) (Val #nm))
    @@ ∅
  <<{ storeSt γ (σ.addIx nids) }>>
  {{ (err : GoInterface), RET #err;
      ⌜(nameClash σ.fnIds nids ∧ err ≠ interface.nil) ∨
        (¬ nameClash σ.fnIds nids ∧ err = interface.nil)⌝ ∗ nm ↦${dn} nfv }}

end spec

end cache
end EtcdGrove
end Perennial
