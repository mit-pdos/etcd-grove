/-
`(*indexer).delete(key, value, index)` (`indexer.go`): `key` out of the index's set of `value`
(the set removed once empty). Lean-first (no Rocq counterpart).
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
abbrev indexer.delete.spec : Prop :=
  ∀ (l : Loc) (key value : GoString) (ix : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.store ∗ ownIdx ix (DFrac.own 1) }}
    (App (App (App (Val (l @!! go.GoType.PointerType indexer.ty @!! go!"delete")) (Val #key)) (Val #value)) (Val #ix))
  {{ RET #(); ownIdx ix (DFrac.own 1) }}

end spec

end cacher
end EtcdGrove
end Perennial
