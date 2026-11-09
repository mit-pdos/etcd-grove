/-
`v3rpc.AuthAdmin.requireAuthInfo` (`server/etcdserver/api/v3rpc/`).

Users: `kvServer.Compact`, the maintenance wrappers (`authMaintenanceServer.*`).

Proof sketch: `AuthInfoFromCtx(ctx)` (2c/3d, over `reqPrin ctx who tls`, `reqPrin_of_md`), `AuthStore()` and its `IsAdminPermitted`/`IsAuthEnabled` (3d), at the member's local auth state (no linearization: the callers fire their updates with the refusal, which the model allows at any state, or answer locally).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/AuthAdmin__requireAuthInfo.lean`: over 2c's `reqPrin` and `srvErrOf` (was the auth plan's `authOn` modes: one spec for both).
verify-round (server-core's request): over 2c's persistent `srvErr err e` (the sentinel values by `sentinelAt`), replacing the deprecated pure `srvErrOf`.

Margin: a `nil` result says nothing (the check is at a possibly stale auth state).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3rpc

open Iris Iris.BI EtcdModel EtcdWire ClientV3 Grpc Proto EtcdServer

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `aa.requireAuthInfo(ctx)`: `nil` (auth is off or the request names a user, at the member's auth state), or a server error of one of
[.userEmpty, .invalidAuthToken]. -/
def AuthAdmin.requireAuthInfo.spec : Prop :=
  ∀ (aa s : Loc) (γ : Cluster) (ctx : GoInterface) (who tls : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ authAdminAt aa s γ ∗ Context.ctxOk ctx ∗ reqPrin ctx who tls }}
    (App (Val (aa @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthAdmin.ty @!! go!"requireAuthInfo")) (Val #ctx))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∨ ∃ e, ⌜e ∈ ([.userEmpty, .invalidAuthToken] : List EtcdErr)⌝ ∗ srvErr err e }}

end spec

end V3rpc
end EtcdGrove
end Perennial
