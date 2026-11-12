/-
`(*clientv3.authClient).Authenticate` (`client/v3/auth.go`).

Users: `Client.getToken` (`client.go`: the client's own token, at `New` and on every refresh); through the `Auth` bundle (and the promoted `Client.Authenticate`) (`authAt_methods`, `authHandle_authAt`).

Proof sketch: allocates the request message (`reqOwn`, 3h's `protoRest_zero` and field writes), calls
`auth.remote.Authenticate(ctx, req, auth.callOpts...)` (`authHandle` over a ready client: `remote` a `remoteAuthAt` value,
`callOpts` with `callOptsOk _ false`; `remoteAuthAt_call` at the request: the caller's update,
exclusive (sent at most once: the wrapper does not mark it repeatable), handed over), then `ContextError(ctx, err)` (W0's spec: a definite `.etcd e` becomes
`errVal e`, the reply's `wireReply ansReply` becomes `ansReply`; an indefinite error stays
`indefCall`), and returns the reply pointer converted. The reply carries `tokenOf γ tok name` (2a/3d: the token the server issues names the user it authenticated).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/authClient__Authenticate.lean`: restated over the model (`Step who` of the auth request, any principal, auth on or off, any answer: the old spec was for the admin's set-up only, auth off, with the reply's error only).

Margin: none.

Round 1: the call's principal per call (W0's `ctxPrin who ctx p`); the handle records its client,
ready (`clientReady`: the token refresh reads `c.Auth`).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiClient

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

/-- `a.Authenticate(ctx, ...)`: the request `.authenticate name pw` linearized by the caller's update, or an
error that settles nothing; the call's principal is its context's (`ctxPrin who ctx p`). -/
def authClient.Authenticate.spec : Prop :=
  ∀ (a c : Loc) (γ : Cluster) (who : Principal) (name pw : GoString),
  Call.Triple (a @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty @!! go!"Authenticate")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ authHandle a c γ who ∗ clientReady c) γ who [ #name, #pw]
    (.authenticate name pw)
    (authReply γ name)

end spec

end ClientV3
end EtcdGrove
end Perennial
