/-
`(*watchCache).checkSnapshotResourceVersion(snap, expectedRV)` (`watch_cache.go`): returns, for a
published snapshot at the expected version (otherwise it logs, and panics when
`PanicOnCacheInconsistency` is set). Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.DefsWC

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI k8s_io.apiserver.pkg.storage.cacher

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

/-- See the file header. -/
abbrev watchCache.checkSnapshotResourceVersion.spec : Prop :=
  ∀ (wc : Loc) (p : Loc) (s : List (Loc × GoString)) (rv : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher ∗ isSnap p s rv }}
    (App (App (Val (wc @!! go.GoType.PointerType watchCache.ty @!! go!"checkSnapshotResourceVersion")) (Val #(interface.mkOk (go.GoType.PointerType k8s_io.apiserver.pkg.storage.cacher.store.btreeStore.ty) #p))) (Val #rv))
  {{ RET #(); True }}

end spec

end cacher
end EtcdGrove
end Perennial
