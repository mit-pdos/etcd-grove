/-
`(*storeIndex).getKeysFromIndex(n, obj)` (`thread_safe_store.go:105`): the keys of the sets of the
values the indexer `n` gives `obj`. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (`Index`,
the namespace listers' path).
-/
module

public import Proof.k8s_io.client_go.tools.cache.StoreDefs

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

/-- The keys of the sets of the values `vs` in an indexer's index. -/
def keysOfVals (X : IxN) (vs : List GoString) (k : GoString) : Prop := ∃ v ∈ vs, k ∈ viewN X v

/-- A set the caller reads: `nil` (no keys), or a points-to the caller gives back to get `R`. -/
def setRes (s : Loc) (S : KSet) (R : IProp GF) : IProp GF :=
  iprop((⌜s = null ∧ S = ∅⌝ ∗ R) ∨ (∃ dq : DFrac, s ↦${dq} S ∗ (s ↦${dq} S -∗ R)))

/-- **`i.getKeysFromIndex(n, obj)`** (with any shares of the indexers and indices), for `obj`
meeting the index functions' contract: for an indexer `n` (relation `F`), no error and a set of
exactly the keys of the sets of `obj`'s values `vq` (`F obj vq`; the index's own set when there is
one value, a fresh set otherwise), which gives the indices back; otherwise an error. -/
abbrev storeIndex.getKeysFromIndex.spec : Prop :=
  ∀ (i im ip : Loc) (dqi dqm dq : DFrac) (fv : GMap GoString GoFunc) (fns : GMap GoString (Fn GF))
    (ix : Ix) (OK : GoInterface → IProp GF) (n : GoString) (obj : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      structFieldRef storeIndex go!"indexers" i ↦{dqi} im ∗ im ↦${dqm} fv ∗ fnsOk OK fv fns ∗
      structFieldRef storeIndex go!"indices" i ↦{dq} ip ∗ ownIx ip dq ix ∗ □ OK obj }}
    (App (App (Val (i @!! go.GoType.PointerType storeIndex.ty @!! go!"getKeysFromIndex"))
      (Val #n)) (Val #obj))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      structFieldRef storeIndex go!"indexers" i ↦{dqi} im ∗ im ↦${dqm} fv ∗
      structFieldRef storeIndex go!"indices" i ↦{dq} ip ∗
      match fns !! n with
      | none => ⌜err ≠ interface.nil⌝ ∗ ownIx ip dq ix
      | some F => ⌜err = interface.nil⌝ ∗ ∃ (S : KSet) (vq : List GoString),
          ⌜∀ k, k ∈ S ↔ keysOfVals (ixAt ix n) vq k⌝ ∗ □ F obj vq ∗ setRes s S (ownIx ip dq ix) }}

end spec

end cache
end EtcdGrove
end Perennial
