/-
`(*watchCache).getLatestSnapshotLocked(ctx, false, matchValues)` (`watch_cache.go`), for a
non-recursive read (`WaitUntilFreshAndGet`'s; a recursive one may use an index's snapshot): under
the lock (the lock's resource at some fraction `q`, of the state `st`), the store's latest snapshot,
which is of `st` (the writer's token's part, `wcsOwn γ q st`, agrees with the published state at
the load), with the caller's fact `Ψ st`, and no index. Lean-first (no Rocq counterpart).
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
abbrev watchCache.getLatestSnapshotLocked.spec : Prop :=
  ∀ (wc : Loc) (γ : WCSNames) (Ψ : SnapSt → IProp GF) (ctx : GoInterface) (mv : GoSlice)
    (q : Qp) (st : SnapSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher ∗ isWC wc γ Ψ ∗ wcLockPSt wc γ q st }}
    (App (App (App (Val (wc @!! go.GoType.PointerType watchCache.ty @!! go!"getLatestSnapshotLocked")) (Val #ctx)) (Val #false)) (Val #mv))
  {{ (p : Loc), RET (PairV #(interface.mkOk (go.GoType.PointerType k8s_io.apiserver.pkg.storage.cacher.store.btreeStore.ty) #p) #(go!"" : GoString));
      wcLockPSt wc γ q st ∗ isSnap p st.1 st.2 ∗ □ Ψ st }}

end spec

end cacher
end EtcdGrove
end Perennial
