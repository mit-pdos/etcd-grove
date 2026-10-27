/-
`(*snapshotter).UpdateResourceVersion(rv)` (`snapshotter.go`): the snapshotter's version is `rv`
(if enabled), not before the store's previous version. (On an earlier one, it panics when
`PanicOnCacheInconsistency` is set: excluded by `ownSnapshotter`'s bound and the premise.) Lean-first (no Rocq counterpart).
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
abbrev snapshotter.UpdateResourceVersion.spec : Prop :=
  ∀ (l : Loc) (rv0 : w64) (rv : w64),
  uint.Z rv0 ≤ uint.Z rv →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.store ∗ ownSnapshotter l (DFrac.own 1) rv0 }}
    (App (Val (l @!! go.GoType.PointerType snapshotter.ty @!! go!"UpdateResourceVersion")) (Val #rv))
  {{ RET #(); ownSnapshotter l (DFrac.own 1) rv }}

end spec

end cacher
end EtcdGrove
end Perennial
