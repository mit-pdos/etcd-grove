/-
`(*clientv3.authClient).RoleGrantPermission` (`client/v3/auth.go`).

Users: `examples/etcd/auth/authkv.go` (`SetUp`: a read-write range), snippet `clientv3client/auth.go`; through the `Auth` bundle (and the promoted `Client.RoleGrantPermission`) (`authAt_methods`, `authHandle_authAt`).

Proof sketch: allocates the request message (`reqOwn`, 3h's `protoRest_zero` and field writes), calls
`auth.remote.RoleGrantPermission(ctx, req, auth.callOpts...)` (`authHandle` over a ready client: `remote` a `remoteAuthAt` value,
`callOpts` with `callOptsOk _ false`; `remoteAuthAt_call` at the request: the caller's update,
exclusive (sent at most once: the wrapper does not mark it repeatable), handed over), then `ContextError(ctx, err)` (W0's spec: a definite `.etcd e` becomes
`errVal e`, the reply's `wireReply ansReply` becomes `ansReply`; an indefinite error stays
`indefCall`), and returns the reply pointer converted. The permission message is built from the strings' bytes and the type converted (`authpb.Permission_Type(permType)`); a type outside the model's three (`permTypeM`) is a scope restriction (the server stores any `int32`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/authClient__RoleGrantPermission.lean`: restated over the model (`Step who` of the auth request, any principal, auth on or off, any answer: the old spec was for the admin's set-up only, auth off, with the reply's error only).

Margin: none.

Round 1: the call's principal per call (W0's `ctxPrin who ctx p`); the handle records its client,
ready (`clientReady`: the token refresh reads `c.Auth`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiClient

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

/-- `a.RoleGrantPermission(ctx, ...)`: the request `.roleGrantPermission name { permType := pt, range := { key := key, rangeEnd := rangeEnd } }` linearized by the caller's update, or an
error that settles nothing; the call's principal is its context's (`ctxPrin who ctx p`). -/
def authClient.RoleGrantPermission.spec : Prop :=
  ∀ (a c : Loc) (γ : Cluster) (who : Principal) (name key rangeEnd : GoString) (t : w32) (pt : PermType),
  permTypeM t = some pt →
  Call.Triple (a @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty @!! go!"RoleGrantPermission")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ authHandle a c γ who ∗ clientReady c) γ who [ #name, #key, #rangeEnd, #t]
    (.roleGrantPermission name { permType := pt, range := { key := key, rangeEnd := rangeEnd } })

end spec

end ClientV3
end EtcdGrove
end Perennial
