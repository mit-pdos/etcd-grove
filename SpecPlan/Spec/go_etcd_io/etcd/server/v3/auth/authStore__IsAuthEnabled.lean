/-
## `(*authStore).IsAuthEnabled()`

**Users.** `isOpPermitted`, `IsAdminPermitted`, `Authenticate`, `CheckPassword`, `AuthInfoFromCtx`,
`WithRoot` (this package); `EtcdServer.requireAuthInfo` and the lease checks (`v3_server.go:576,609,
719,754,1278`, 2c); the gateway's certificate guard (`embed/serve.go:465`); `AuthAdmin.requireAuthInfo` (`api/v3rpc/auth.go:192`, 2a); `applierV3backend.
AuthStatus` (`apply/backend.go:152`, 3a, the writer). Snippet: `examples/specreq/auth/check.go`
(`ReqEnabledFlag`).

**Proof sketch.** `enabledMu.RLock()` (a reader slot: the caller's `threadTok`, lent), `as.enabled`
under `enabledMu`'s invariant: the flag view, at a recorded state at or after every `authLb`;
`RUnlock`.

**Changes.** The old mode verdict (`enabledVerdict M`) restated as a recorded state's flag.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.auth.Api

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

/-- **`as.IsAuthEnabled()`**: the flag of a recorded state at or after the lower bound `i0`. -/
def authStore.IsAuthEnabled.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (i0 : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authLb γa i0 ∗ threadTok }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"IsAuthEnabled")) (Val #()))
  {{ (b : Bool), RET #b; threadTok ∗
      ∃ (j : Nat) (a : AuthState), ⌜i0 ≤ j ∧ a.enabled = b⌝ ∗ authAt γa j a }}

end spec
end Auth
end EtcdGrove
end Perennial
