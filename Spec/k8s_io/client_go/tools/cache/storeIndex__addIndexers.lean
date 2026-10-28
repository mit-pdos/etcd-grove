/-
`(*storeIndex).addIndexers(newIndexers)` (`thread_safe_store.go:155`): adds the new indexers to the
indexers' map unless a name is already taken. Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.StoreDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

/-- Some name is in both maps (`addIndexers`' conflict). -/
def nameClash {V W : Type} (a : GMap GoString V) (b : GMap GoString W) : Prop :=
  ∃ n, (a !! n).isSome ∧ (b !! n).isSome

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- `i.addIndexers(nm)`, the new indexers' map `nm` read only (at most `2^62` of them, the bound of
`sets.List`'s sort): if a new name is already an indexer's, an error and nothing changed;
otherwise no error and the new indexers added (`nfv ∪ fv`). Under the store's write lock, which
holds the indexers' map. -/
abbrev storeIndex.addIndexers.spec : Prop :=
  ∀ (i im nm : Loc) (dqi dn : DFrac) (fv nfv : GMap GoString GoFunc), GMap.size nfv ≤ 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      structFieldRef storeIndex go!"indexers" i ↦{dqi} im ∗ im ↦$ fv ∗ nm ↦${dn} nfv }}
    (App (Val (i @!! go.GoType.PointerType storeIndex.ty @!! go!"addIndexers")) (Val #nm))
  {{ (err : GoInterface), RET #err;
      structFieldRef storeIndex go!"indexers" i ↦{dqi} im ∗ nm ↦${dn} nfv ∗
      (⌜nameClash fv nfv ∧ err ≠ interface.nil⌝ ∗ im ↦$ fv ∨
       ⌜¬ nameClash fv nfv ∧ err = interface.nil⌝ ∗ im ↦$ (nfv ∪ fv)) }}

end spec

end cache
end EtcdGrove
end Perennial
