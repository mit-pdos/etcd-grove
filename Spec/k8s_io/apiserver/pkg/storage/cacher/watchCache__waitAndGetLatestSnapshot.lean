/-
`(*watchCache).waitAndGetLatestSnapshot(ctx, false, minResourceVersion, matchValues)`
(`watch_cache.go`), for a non-recursive read: under the read lock (a reader's token, given back),
waits until the cache is at `minResourceVersion` or later (`waitUntilFreshLocked`); then the store's
latest snapshot, which is the cache's state (`getLatestSnapshotLocked`), its version, no index and no
error; or an error (the wait timed out). Lean-first (no Rocq counterpart).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

/-- See the file header. -/
abbrev watchCache.waitAndGetLatestSnapshot.spec : Prop :=
  ∀ (wc : Loc) (γ : WCSNames) (Ψ : SnapSt → IProp GF) (ctx : GoInterface) (minRV : w64)
    (mv : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher ∗ isWC wc γ Ψ ∗ sync.ownRWMutex (structFieldRef watchCache go!"RWMutex" wc) (wcLockP wc γ) }}
    (App (App (App (App (Val (wc @!! go.GoType.PointerType watchCache.ty @!! go!"waitAndGetLatestSnapshot")) (Val #ctx)) (Val #false)) (Val #minRV))
      (Val #mv))
  {{ (snap : GoInterface) (rv : w64) (idx : GoString) (err : GoInterface),
      RET (PairV (PairV (PairV #snap #rv) #idx) #err);
      sync.ownRWMutex (structFieldRef watchCache go!"RWMutex" wc) (wcLockP wc γ) ∗
      (⌜err = GoInterface.nil⌝ -∗ ∃ (p : Loc) (st : SnapSt),
        ⌜snap = interface.mkOk (go.GoType.PointerType k8s_io.apiserver.pkg.storage.cacher.store.btreeStore.ty) #p ∧ rv = st.2 ∧ (minRV = W64 0 ∨ uint.Z minRV ≤ uint.Z st.2)⌝ ∗
        isSnap p st.1 st.2 ∗ □ Ψ st) }}

end spec

end cacher
end EtcdGrove
end Perennial
