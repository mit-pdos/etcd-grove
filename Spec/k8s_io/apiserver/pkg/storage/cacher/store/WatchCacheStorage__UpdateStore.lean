/-
`(*WatchCacheStorage).UpdateStore(eventType, elem, rv)` (`watch_cache_storage.go`): for an added or
modified object, the element replaces the one with its key (or is added); for a deleted one, the
element with its key is removed; the store is at `rv` and the new state is published
(`latestSnapshot`, and a stored snapshot); the previous element with the key (`nil` if none) is
returned, and no error. For the writer (`wcsOwn`), at a resource version past the current one (the
snapshotter panics on a non-increasing one when `PanicOnCacheInconsistency` is set), for one of the
three event types (another one is an error, which the watch cache never passes). Lean-first (no Rocq counterpart).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.store.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

/-- See the file header. -/
abbrev WatchCacheStorage.UpdateStore.spec : Prop :=
  ∀ (w : Loc) (γ : WCSNames) (et : GoString) (e : Loc) (k : GoString) (st : SnapSt) (rv : w64),
  uint.Z st.2 < uint.Z rv →
  (et = go!"ADDED" ∨ et = go!"MODIFIED" ∨ et = go!"DELETED") →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.store ∗ isWCS w γ ∗ wcsOwn γ st ∗ isElem e k }}
    (App (App (App (Val (w @!! go.GoType.PointerType WatchCacheStorage.ty @!! go!"UpdateStore")) (Val #et)) (Val #e)) (Val #rv))
  {{ RET (PairV #(lookupElem st.1 k) #GoInterface.nil);
      wcsOwn γ (if et = go!"DELETED" then btree.delete st.1 k
                else btree.insert go.GoStringLt st.1 (e, k), rv) }}

end spec

end cacher
end EtcdGrove
end Perennial
