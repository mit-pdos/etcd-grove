/-
`(*storeIndex).updateIndices(oldObj, newObj, key)` (`thread_safe_store.go:226`): every indexer's
index moved from the key's old object to its new one. Lean-first.
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

/-- `i.updateIndices(old, new, key)`, where the items change from `it` to `it'` at `key` only, from
`old` to `new` (`nil` for none; each `nil` or meeting `OK`): the indices, exact for `it` under
the indexers `fns`, become exact for `it'`. Under the store's write lock. -/
abbrev storeIndex.updateIndices.spec : Prop :=
  ∀ (i im ip : Loc) (dqi : DFrac) (qm : Qp) (fv : GMap GoString GoFunc) (fns : GMap GoString Fn)
    (ix : Ix) (OK : GoInterface → IProp GF) (it it' : Items) (key : GoString)
    (old new : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      structFieldRef storeIndex go!"indexers" i ↦{dqi} im ∗ im ↦${DFrac.own qm} fv ∗ fnsOk OK fv fns ∗
      okNil OK old ∗ okNil OK new ∗
      structFieldRef storeIndex go!"indices" i ↦ ip ∗ ownIx ip (DFrac.own 1) ix ∗
      ⌜ixOk fns it ix ∧ old = objAt it key ∧ new = objAt it' key ∧
        ∀ k, k ≠ key → objAt it' k = objAt it k⌝ }}
    (App (App (App (Val (i @!! go.GoType.PointerType storeIndex.ty @!! go!"updateIndices"))
      (Val #old)) (Val #new)) (Val #key))
  {{ RET #(); ∃ ix' : Ix,
      structFieldRef storeIndex go!"indexers" i ↦{dqi} im ∗ im ↦${DFrac.own qm} fv ∗
      structFieldRef storeIndex go!"indices" i ↦ ip ∗ ownIx ip (DFrac.own 1) ix' ∗
      ⌜ixOk fns it' ix'⌝ }}

end spec

end cache
end EtcdGrove
end Perennial
