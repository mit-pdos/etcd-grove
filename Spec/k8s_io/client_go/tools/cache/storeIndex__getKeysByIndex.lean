/-
`(*storeIndex).getKeysByIndex(indexName, indexedValue)` (`thread_safe_store.go:136`): the set of
the value's keys in the indexer's index (shared, not a copy). Lean-first.
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- `i.getKeysByIndex(n, v)` (with any shares of the indexers and indices): for an indexer `n`,
no error and the location of `v`'s set in its index (`setLoc`, `nil` if none); otherwise an
error. -/
abbrev storeIndex.getKeysByIndex.spec : Prop :=
  ∀ (i im ip : Loc) (dqi dqm dq : DFrac) (fv : GMap GoString GoFunc) (fns : GMap GoString Fn)
    (ix : Ix) (OK : GoInterface → IProp GF) (n v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      structFieldRef storeIndex go!"indexers" i ↦{dqi} im ∗ im ↦${dqm} fv ∗ fnsOk OK fv fns ∗
      structFieldRef storeIndex go!"indices" i ↦{dq} ip ∗ ownIx ip dq ix }}
    (App (App (Val (i @!! go.GoType.PointerType storeIndex.ty @!! go!"getKeysByIndex"))
      (Val #n)) (Val #v))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      structFieldRef storeIndex go!"indexers" i ↦{dqi} im ∗ im ↦${dqm} fv ∗
      structFieldRef storeIndex go!"indices" i ↦{dq} ip ∗ ownIx ip dq ix ∗
      ⌜(n ∈ fns → err = interface.nil ∧ s = setLoc ix n v) ∧
        (n ∉ fns → err ≠ interface.nil)⌝ }}

end spec

end cache
end EtcdGrove
end Perennial
