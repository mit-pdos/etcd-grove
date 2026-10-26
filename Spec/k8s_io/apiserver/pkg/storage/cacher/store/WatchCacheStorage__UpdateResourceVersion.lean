/-
`(*WatchCacheStorage).UpdateResourceVersion(rv)` (`watch_cache_storage.go`): the store (its
entries unchanged) is at `rv`, and published. For the writer, with the caller's fact `Ψ` of the new state, at a resource version not before the
current one (the snapshotter panics on an earlier one when `PanicOnCacheInconsistency` is set). Lean-first (no Rocq counterpart).
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
abbrev WatchCacheStorage.UpdateResourceVersion.spec : Prop :=
  ∀ (w : Loc) (γ : WCSNames) (Ψ : SnapSt → IProp GF) (st : SnapSt) (rv : w64),
  uint.Z st.2 ≤ uint.Z rv →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.store ∗ isWCS w γ Ψ ∗
      wcsOwn γ 1 st ∗ □ Ψ (st.1, rv) }}
    (App (Val (w @!! go.GoType.PointerType WatchCacheStorage.ty @!! go!"UpdateResourceVersion")) (Val #rv))
  {{ RET #(); wcsOwn γ 1 (st.1, rv) }}

end spec

end cacher
end EtcdGrove
end Perennial
