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

/-- `i.updateIndices(old, new, key)`, where `key`'s object changes from `old` to `new` (`nil` for
none; each `nil` or meeting `OK`), the indices exact for the recorded values `iv` (`ixOk`), `old`'s
values those recorded for `key` (`valsOk`): the indices become exact for `iv` with `key`'s values
`new`'s (`vs`, each indexer's relation holding of them; under other names the old ones). Under the
store's write lock. -/
abbrev storeIndex.updateIndices.spec : Prop :=
  ∀ (i im ip : Loc) (dqi : DFrac) (qm : Qp) (fv : GMap GoString GoFunc)
    (fns : GMap GoString (Fn GF)) (ix : Ix) (OK : GoInterface → IProp GF) (iv : IV)
    (key : GoString) (old new : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗
      structFieldRef storeIndex go!"indexers" i ↦{dqi} im ∗ im ↦${DFrac.own qm} fv ∗ fnsOk OK fv fns ∗
      okNil OK old ∗ okNil OK new ∗ valsOk fns old (ivOf iv key) ∗
      structFieldRef storeIndex go!"indices" i ↦ ip ∗ ownIx ip (DFrac.own 1) ix ∗
      ⌜ixOk fns iv ix⌝ }}
    (App (App (App (Val (i @!! go.GoType.PointerType storeIndex.ty @!! go!"updateIndices"))
      (Val #old)) (Val #new)) (Val #key))
  {{ RET #(); ∃ (ix' : Ix) (vs : Vals),
      structFieldRef storeIndex go!"indexers" i ↦{dqi} im ∗ im ↦${DFrac.own qm} fv ∗
      structFieldRef storeIndex go!"indices" i ↦ ip ∗ ownIx ip (DFrac.own 1) ix' ∗
      valsOk fns new vs ∗
      ⌜ixOk fns (<[key := vs]> iv) ix' ∧ ∀ n, n ∉ fns → vsAt vs n = ivAt iv n key⌝ }}

end spec

end cache
end EtcdGrove
end Perennial
