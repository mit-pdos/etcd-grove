/-
## `(*authStore).AuthEnable()`

**Users.** `applierV3backend.AuthEnable` (`apply/backend.go:139`), behind the administrator check.
Snippet: `examples/specreq/auth/admin.go` (`ReqAdminSteps`).

**Proof sketch.** `enabledMu.Lock()` (the flag's other half: readers of `IsAuthEnabled` wait);
already enabled: no change, `nil`. The batch transaction (4b's `authBatchTx.Lock`: its
`LockInsideApply` runs the backend's post-lock hook from the caller's `Pre`, `authBeHook`): `root` read; absent:
`ErrRootUserNotExist`; without the root role (`hasRootRole`): `ErrRootRoleNotExist`; else the flag
saved, `as.enabled = true` (the linearization point: `storeNext .authEnable [] a`, enabled, recorded, with the writer's `authReached`),
the provider's `enable()` (the simple provider's keeper started, on the token the provider holds),
the cache refreshed, `setRevision` of the stored revision (the same value: `AuthEnable` keeps the
revision, W0's model), the deferred `Unlock` and `ForceCommit`, then `enabledMu.Unlock()` (the flag
view moves last).

**Changes.** The old per-mode spec restated over `admStep`; round 1: the one next state
`storeNext` (review F1, F2).

Integration I5: the post-lock hook (`authBeHook` of the store's backend `authBeCur`, `hookOut`), which 4b's `authBatchTx.Lock` needs.
Re-review (N1): the hook is the current backend's, `authBeCur γa be ∗ authBeHook be Pre Q`, given back
with `authBeCur` (the store-indexed `authHook` is gone).

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Auth

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`as.AuthEnable()`** by the writer: W0's `authEnable` effect, recorded; `nil` or the
package's error of the answer. -/
def authStore.AuthEnable.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (i : Nat) (a : AuthState) (be : GoInterface) (Pre Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authCur γa i a ∗ authReached γ (storeNext .authEnable [] a) ∗
      authBeCur γa be ∗ Pre ∗ authBeHook be Pre Q }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"AuthEnable")) (Val #()))
  {{ (err : GoInterface), RET #err; authBeCur γa be ∗ hookOut be Pre Q ∗
      ∃ res : Resp, ⌜admStep .authEnable a (storeNext .authEnable [] a) res⌝ ∗
        authCur γa (i + 1) (storeNext .authEnable [] a) ∗
        (⌜res = .ok .authEnable ∧ err = GoInterface.nil⌝ ∨
         ∃ e ae, ⌜res = .err e ∧ ae.etcd = some e⌝ ∗ errIs ae err) }}

end spec
end Auth
end EtcdGrove
end Perennial
