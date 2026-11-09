/-
## `(*authStore).AuthInfoFromCtx(ctx)`

**Users.** `EtcdServer.AuthInfoFromCtx` (`v3_server.go:1207`, 2c), through it every request's
principal: `processInternalRaftRequestOnce`, `doSerialize`, `requireAuthInfo`, the lease checks (2c),
the gRPC guards `AuthAdmin` (2a), the watch create (2b). Snippets: `examples/specreq/auth/token.go`
(`ReqTokenUser`, `ReqNoToken`).

**Proof sketch.** The flag (`IsAuthEnabled`: off, `nil, nil`, at a recorded state with auth off);
`metadata.FromIncomingContext(ctx)` (2a's boundary: `ctxInMD`, grpc's; none: `nil, nil`); the `token` or
`authorization` key's first value (non-empty lists: `ctxToken`'s `tokKeysOk`), `Bearer ` trimmed (`mdToken`);
`authInfoFromToken` (the provider's `info(ctx, token, Revision())`: `tokenProviderAt`'s contract,
`tokenUser γ tok u` for an `AuthInfo` naming `u`; the simple provider waits for the token's index to
be applied, `waiterOk` under the gate `□ R`, or for `ctx` to be done: `Context.ctxOk`); not valid: `redactToken`, a
warning, `ErrInvalidAuthToken`.

**Changes.** The old `ctxBound`/`ctxTokenOf` (per mode) restated over the context's token
(`ctxToken`) and W0's `tokenUser`: a token is mapped to the user the cluster issued it to, at every
mode. The auth revision is not stated (see Margin).
Verify round (A9 3d F5, F7): the context's predicates are grpc's (`Auth.ctxInMD` is
`Grpc.ctxInMD`), with the token keys' values non-empty a premise (`ctxToken`'s `tokKeysOk`: a run's
context gives it by `Grpc.rpcCtx_vals`; it was in the provisional `ctxInMD`'s meaning); the
provider's gate `authGate γa R ∗ □ R` (the simple provider's waiter is the server's, usable once it
started: `R := srvStarted`); the error is the global's value (`errIs`).

**Margin.** The `AuthInfo`'s revision (the store's `Revision()` for the simple provider, the
token's claim for JWT) is not stated: no caller's argument can use it soundly
(`nonissues/etcd-auth-revision-before-visible.md`); the checks treat any value. Whether auth was on
is stated only for the `nil` answer.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Api
public import Spec.context.Api

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

/-- **`as.AuthInfoFromCtx(ctx)`** for a context carrying the token `o`: `nil, nil` (no token, or
auth off at a recorded state), an `AuthInfo` naming the user the cluster issued the token to, or
`ErrInvalidAuthToken` (a token the member does not accept: expired, invalidated, of another
member's simple provider, ...). -/
def authStore.AuthInfoFromCtx.spec : Prop :=
  ∀ (st : Loc) (γ : Cluster) (γa : AuthNames) (R : IProp GF) (i0 : Nat) (ctx : GoInterface)
    (o : Option GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authGate γa R ∗ □ R ∗ authLb γa i0 ∗ threadTok ∗ Context.ctxOk ctx ∗ ctxToken ctx o }}
    (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"AuthInfoFromCtx")) (Val #ctx))
  {{ (ai : Loc) (err : GoInterface), RET (PairV #ai #err); threadTok ∗
      ((⌜ai = null ∧ err = GoInterface.nil⌝ ∗
          (⌜o = none⌝ ∨ ∃ (j : Nat) (a : AuthState), ⌜i0 ≤ j ∧ a.enabled = false⌝ ∗ authAt γa j a)) ∨
       (⌜err = GoInterface.nil⌝ ∗ ∃ (tok u : GoString) (rev : w64), ⌜o = some tok⌝ ∗
          tokenUser γ tok u ∗ authInfoAt ai DFrac.discard u rev) ∨
       (⌜ai = null ∧ o ≠ none⌝ ∗ errIs .invalidAuthToken err)) }}

end spec
end Auth
end EtcdGrove
end Perennial
