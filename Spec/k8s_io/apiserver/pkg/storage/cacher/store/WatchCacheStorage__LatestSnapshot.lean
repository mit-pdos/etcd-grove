/-
`(*WatchCacheStorage).LatestSnapshot()` (`watch_cache_storage.go`): the published snapshot, loaded
without a lock (an atomic load of `latestSnapshot`): a snapshot of the published state `st` at the
load, at which the caller's view shift runs against the published state (`wcsPub γ st`, the
invariant's quarter of the state), turning `P` into `Q st` (it may open other invariants); with the caller's fact `Ψ st` of every
published state. With `P` and `Q` trivial, some published snapshot; with part of the writer's
token in `P` (a reader under the watch cache's read lock), the current state (the token agrees
with the invariant's quarter). Lean-first (no Rocq counterpart).
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
abbrev WatchCacheStorage.LatestSnapshot.spec : Prop :=
  ∀ (w : Loc) (γ : WCSNames) (Ψ : SnapSt → IProp GF) (P : IProp GF) (Q : SnapSt → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher.store ∗ isWCS w γ Ψ ∗ P ∗
      (∀ st : SnapSt, wcsPub γ st -∗ P ={⊤ \ ↑wcsN}=∗ wcsPub γ st ∗ Q st) }}
    (App (Val (w @!! go.GoType.PointerType WatchCacheStorage.ty @!! go!"LatestSnapshot")) (Val #()))
  {{ (p : Loc) (st : SnapSt), RET #(interface.mkOk (go.GoType.PointerType btreeStore.ty) #p);
      isSnap p st.1 st.2 ∗ □ Ψ st ∗ Q st }}

end spec

end cacher
end EtcdGrove
end Perennial
