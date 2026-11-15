/-
## `(*authStore).Authenticate(ctx, username, password)`

**Users.** `applierV3backend.Authenticate` (`apply/backend.go:159`, 3a), the writer, applying an
`InternalAuthenticateRequest` at the entry index `idx` with the context
`WithValue(WithValue(ctx, AuthenticateParamIndex{}, idx), AuthenticateParamSimpleTokenPrefix{}, p)`.
Snippet: `examples/specreq/auth/token.go` (`ReqAuthenticateApply`).

**Proof sketch.** The flag (`IsAuthEnabled`: the writer's `a`; off: `ErrAuthNotEnabled`);
`as.be.GetUser(name)` (4b: a read section of the read transaction, at the writer's `a`, integration I5: was "the batch transaction"; absent or password-less:
`ErrAuthFailed`); `assign(ctx, name, Revision())` (`tokenProviderAt`'s contract from `authnCtx`: the
simple provider's token `p.idx`, fresh since no index above `n < idx` was assigned, `tokFrom`; its
`tokenUser γ tok name` from `authnCtx`'s realization; the no-op provider's `ErrAuthFailed`; JWT's
signed token, `jwtTokOk`); a debug log (`redactToken`); the response. The password is not checked
here (the proposer's `CheckPassword` did).

**Verify round.** `authnCtx` is transparent (A9 3d F4: it was opaque with no introduction), over
the cluster `γ` (the applier builds it with `context.WithValue` twice); the errors are the globals'
values (`errIs`, the sentinel encoding).

**Changes.** The old token binding (`S5`, per mode) restated over W0's `tokenUser`; the simple
provider's right to issue as `tokFrom`.

**Margin.** The provider's error is not named (the no-op provider's is `ErrAuthFailed`). Round 1
(review S11): an absent or password-less user is `ErrAuthFailed` exactly (3a's need).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.auth.Api
public import SpecPlan.Spec.context.Api

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

/-- **`as.Authenticate(ctx, name, pw)`** by the writer: auth off (`ErrAuthNotEnabled`), an error
(the user absent or password-less, the provider's), or a response carrying a token the cluster
issued to `name`. -/
def authStore.Authenticate.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (i : Nat) (a : AuthState) (ctx : GoInterface)
    (name pw : GoString) (n idx : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authCur γa i a ∗ threadTok ∗ tokFrom γa n ∗
      authnCtx γ ctx name idx ∗ ⌜n < idx⌝ ∗ Context.ctxOk ctx }}
    (App (App (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"Authenticate")) (Val #ctx)) (Val #name)) (Val #pw))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); authCur γa i a ∗ threadTok ∗
      tokFrom γa idx ∗
      ((⌜resp = null ∧ a.enabled = false⌝ ∗ errIs .authNotEnabled err) ∨
       (⌜resp = null ∧ a.enabled = true ∧
          ∀ ur, a.users name = some ur → ur.password = none⌝ ∗ errIs .authFailed err) ∨
       ⌜resp = null ∧ err ≠ GoInterface.nil ∧ a.enabled = true ∧
          ∃ ur c, a.users name = some ur ∧ ur.password = some c⌝ ∨
       (⌜err = GoInterface.nil ∧ a.enabled = true ∧
          ∃ ur p, a.users name = some ur ∧ ur.password = some p⌝ ∗
        ∃ tok : GoString, authnRespAt resp tok ∗
          tokenUser γ tok name)) }}

end spec
end Auth
end EtcdGrove
end Perennial
