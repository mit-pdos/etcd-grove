/-
## `(*authStore).AuthDisable()`

**Users.** `applierV3backend.AuthDisable` (`apply/backend.go:147`), behind the administrator
check. Snippet: `examples/specreq/auth/admin.go` (`ReqAdminSteps`).

**Proof sketch.** `enabledMu.Lock()`; disabled: no change. The batch transaction (`authBatchTx.Lock`: the post-lock
hook from `Pre`, `authBeHook`): the flag saved,
`commitRevision` (the linearization point: the next state, disabled with the revision bumped),
`Unlock`, `ForceCommit`, `as.enabled = false`, the provider's `disable()` (the keeper stopped and
waited for, every simple token dropped), `enabledMu.Unlock()`.

**Changes.** The old per-mode spec restated over `admStep`; round 1: the one next state
`storeNext` (review F1, F2).

Integration I5: the post-lock hook (`authBeHook` of the store's backend `authBeCur`, `hookOut`), and `recordsFit` of the next state
(`commitRevision.spec` needs it: the bumped revision fits the atomic).
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

/-- **`as.AuthDisable()`** by the writer: W0's `authDisable` effect, recorded. -/
def authStore.AuthDisable.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (i : Nat) (a : AuthState) (be : GoInterface) (Pre Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authCur γa i a ∗ authReached γ (storeNext .authDisable [] a) ∗
      ⌜recordsFit (storeNext .authDisable [] a)⌝ ∗ authBeCur γa be ∗ Pre ∗ authBeHook be Pre Q }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"AuthDisable")) (Val #()))
  {{ RET #(); authBeCur γa be ∗ hookOut be Pre Q ∗ ∃ res : Resp, ⌜admStep .authDisable a (storeNext .authDisable [] a) res⌝ ∗
      authCur γa (i + 1) (storeNext .authDisable [] a) }}

end spec
end Auth
end EtcdGrove
end Perennial
