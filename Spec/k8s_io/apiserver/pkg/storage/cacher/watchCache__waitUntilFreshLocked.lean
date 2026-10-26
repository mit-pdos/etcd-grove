/-
`(*watchCache).waitUntilFreshLocked(ctx, rv)` (`watch_cache.go`): under the read lock, waits
(on the condition variable, which releases and retakes it) until the cache has caught up to `rv`,
or gives up after `blockTimeout` (an error, `NewTooLargeResourceVersionError`). Without an error,
the cache's state, which the lock's resource holds again, is at `rv` or later (or `rv` is `0`). Lean-first (no Rocq counterpart).
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
abbrev watchCache.waitUntilFreshLocked.spec : Prop :=
  ∀ (wc : Loc) (γ : WCSNames) (Ψ : SnapSt → IProp GF) (ctx : GoInterface) (rv : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher ∗ isWC wc γ Ψ ∗ sync.ownRWMutexRLocked (structFieldRef watchCache go!"RWMutex" wc) (wcLockP wc γ) ∗
      ▷ wcLockP wc γ sync.rfrac }}
    (App (App (Val (wc @!! go.GoType.PointerType watchCache.ty @!! go!"waitUntilFreshLocked")) (Val #ctx)) (Val #rv))
  {{ (err : GoInterface), RET #err; sync.ownRWMutexRLocked (structFieldRef watchCache go!"RWMutex" wc) (wcLockP wc γ) ∗
      ∃ st : SnapSt, wcLockPSt wc γ sync.rfrac st ∗
        ⌜err = GoInterface.nil → rv = W64 0 ∨ uint.Z rv ≤ uint.Z st.2⌝ }}

end spec

end cacher
end EtcdGrove
end Perennial
