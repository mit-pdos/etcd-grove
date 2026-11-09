/-
## `(*authStore).AuthDisable()`

**Users.** `applierV3backend.AuthDisable` (`apply/backend.go:147`), behind the administrator
check. Snippet: `examples/specreq/auth/admin.go` (`ReqAdminSteps`).

**Proof sketch.** `enabledMu.Lock()`; disabled: no change. The batch transaction: the flag saved,
`commitRevision` (the linearization point: the next state, disabled with the revision bumped),
`Unlock`, `ForceCommit`, `as.enabled = false`, the provider's `disable()` (the keeper stopped and
waited for, every simple token dropped), `enabledMu.Unlock()`.

**Changes.** The old per-mode spec restated over `admStep`.

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
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (i : Nat) (a : AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authCur γa i a ∗ admNext γ .authDisable a }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"AuthDisable")) (Val #()))
  {{ RET #(); ∃ (a' : AuthState) (res : Resp), ⌜admStep .authDisable a a' res⌝ ∗
      authCur γa (i + 1) a' }}

end spec
end Auth
end EtcdGrove
end Perennial
