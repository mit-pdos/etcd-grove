/-
`(*clientv3.authClient).UserAddWithOptions` (`client/v3/auth.go`).

Users: no user in scope (etcdctl); through the `Auth` bundle (`authAt_methods`, `authHandle_authAt`).

Proof sketch: allocates the request message (`reqOwn`, 3h's `protoRest_zero` and field writes), calls
`auth.remote.UserAdd(ctx, req, auth.callOpts...)` (`authHandle`: `remote` a `remoteAuthAt` value,
`callOpts` with `callOptsOk _ false`; `remoteAuthAt_call` at the request: the caller's update,
exclusive (sent at most once: the wrapper does not mark it repeatable), handed over), then `ContextError(ctx, err)` (W0's spec: a definite `.etcd e` becomes
`errVal e`, the reply's `wireReply ansReply` becomes `ansReply`; an indefinite error stays
`indefCall`), and returns the reply pointer converted. The options pointer is converted (`(*authpb.UserAddOptions)(options)`) and sent as the request's `Options` (`userAddOptsAt`: `nil` means a password is required).

Changes: new (no old spec): the `Auth` bundle needs every method.

Margin: none.
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

/-- `a.UserAddWithOptions(ctx, ...)`: the request `.userAdd name pw noPw` linearized by the caller's update, or an
error that settles nothing. -/
def authClient.UserAddWithOptions.spec : Prop :=
  ∀ (a : Loc) (γ : Cluster) (who : Principal) (name pw : GoString) (o : Loc) (noPw : Bool),
  Auth.Triple (a @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.authClient.ty @!! go!"UserAddWithOptions")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ authHandle a γ who ∗ userAddOptsAt o noPw) γ who [ #name, #pw, #o]
    (.userAdd name pw noPw)

end spec

end ClientV3
end EtcdGrove
end Perennial
