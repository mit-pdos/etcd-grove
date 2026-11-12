/-
`(*clientv3.Client).getToken` (`client/v3/client.go`).

Users: `newClient` (the first token), `refreshToken` (the unary interceptor's refresh), the stream
interceptor (before every stream); snippet `clientv3client/auth.go` (`ReqPasswordChangeRefresh`).

Proof sketch: a token configured: `UpdateAuthToken(c.Token)` (`bundleAt`: the token names `who`,
`cfgPrincipal_token`). No user name or password: `nil`. Else `c.Auth.Authenticate(ctx, Username,
Password)` (`clientCore` with `clientReady c`: `authAt` of the set `Auth` field; the update built from `idUpd γ`: an
authentication changes nothing); `ErrAuthNotEnabled` (`errors.Is`, W0's `errorsIs_errVal`): the
token `""`, `nil`; another error returned (`ContextError`'d by `Authenticate`: `errVal e` of a
definite answer, `ErrAuthFailed` and the refusals; else indefinite); a token (`authReply`:
`tokenUser γ tok Username`) into the bundle.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Client__getToken.lean` (`clientTokAt` with a
caller's token predicate `P`): the token names the client's principal (`bundleAt`).

Margin: an authentication's other definite answers are not refusals (only `authFailed` and
`authNotEnabled` are possible besides them, `authStep`).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.getToken(ctx)`: the bundle's token refreshed for `who`; `nil`, an indefinite error, or a
refusal (`ErrAuthFailed`: the password changed or the user deleted). -/
def Client.getToken.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (p : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientCore c γ who ∗ clientReady c ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"getToken")) (Val #ctx))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∨ indefCall err ∨
      ∃ e, callErr err (.etcd e) ∗ ⌜e.refusal = true⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
