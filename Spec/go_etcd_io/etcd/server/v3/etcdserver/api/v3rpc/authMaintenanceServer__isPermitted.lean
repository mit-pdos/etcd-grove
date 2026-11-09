/-
`v3rpc.authMaintenanceServer.isPermitted` (`server/etcdserver/api/v3rpc/`).

Users: the maintenance wrappers (the promoted method of the embedded `*AuthAdmin`).

Proof sketch: `AuthInfoFromCtx(ctx)` (2c/3d, over `reqPrin ctx who tls`, `reqPrin_of_md`), `AuthStore()` and its `IsAdminPermitted`/`IsAuthEnabled` (3d), at the member's local auth state (no linearization: the callers fire their updates with the refusal, which the model allows at any state, or answer locally).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/authMaintenanceServer__isPermitted.lean`: over 2c's `reqPrin` and `srvErrOf` (was the auth plan's `authOn` modes: one spec for both).

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

/-- `aa.isPermitted(ctx)`: `nil` (the user has the root role (or auth is off), at the member's auth state), or a server error of one of
[.userEmpty, .userNotFound, .permissionDenied, .invalidAuthToken]. -/
def authMaintenanceServer.isPermitted.spec : Prop :=
  ∀ (aa s : Loc) (γ : Cluster) (ctx : GoInterface) (who tls : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ authMaintAt aa s γ ∗ Context.ctxOk ctx ∗ reqPrin ctx who tls }}
    (App (Val (aa @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer.ty @!! go!"isPermitted")) (Val #ctx))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil ∨ ∃ e ∈ ([.userEmpty, .userNotFound, .permissionDenied, .invalidAuthToken] : List EtcdErr), srvErrOf err e⌝ }}

end spec

end V3rpc
end EtcdGrove
end Perennial
