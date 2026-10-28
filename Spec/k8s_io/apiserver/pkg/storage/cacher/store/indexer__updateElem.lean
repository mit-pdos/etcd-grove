/-
`(*indexer).updateElem(key, oldObj, newObj, rv)` (`indexer.go`), which moves `key` from the old
element's index values to the new one's (either may be `nil`): the indexer stays well-formed
(`ownIndexer`; what the indices hold is not specified: no read through an index is verified yet)
and there is no error, since the index functions never fail (`ownIndexer`'s `isIndexFn`, the
premise of the store's specs: `issues/k8s-watchcache-index-error-partial-update.md`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.store.DefsWCS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI k8s_io.apiserver.pkg.storage.cacher.store

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.store.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

/-- See the file header. -/
abbrev indexer.updateElem.spec : Prop :=
  ∀ (l : Loc) (key : GoString) (old new : Loc) (rv : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.store ∗ ownIndexer l (DFrac.own 1) ∗ (⌜old = null⌝ ∨ isElem old key) ∗
      (⌜new = null⌝ ∨ isElem new key) }}
    (App (App (App (App (Val (l @!! go.GoType.PointerType indexer.ty @!! go!"updateElem")) (Val #key)) (Val #old)) (Val #new)) (Val #rv))
  {{ RET #GoInterface.nil; ownIndexer l (DFrac.own 1) }}

end spec

end cacher
end EtcdGrove
end Perennial
