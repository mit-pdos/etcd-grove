/-
`v3rpc.AuthAdmin.isPermitted` (`server/etcdserver/api/v3rpc/`).

Users: `kvServer.Compact`, the maintenance wrappers (`authMaintenanceServer.*`).

Proof sketch: `AuthInfoFromCtx(ctx)` (2c/3d, over `reqPrin ctx who tls`, `reqPrin_of_md`: `who` when it reads auth on, `tls` (none without `--client-cert-auth`) when it reads it off or finds no token), `AuthStore()` and its `IsAdminPermitted`/`IsAuthEnabled` (3d), at the member's local auth state (no linearization: the callers fire their updates with the refusal, which the model allows at any state, or answer locally).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/AuthAdmin__isPermitted.lean`: over 2c's `reqPrin` and `srvErrOf` (was the auth plan's `authOn` modes: one spec for both).
verify-round (server-core's request): over 2c's persistent `srvErr err e` (the sentinel values by `sentinelAt`), replacing the deprecated pure `srvErrOf`.

verify-round (A6 F5): the denial says at which tables (`adminDenied` over `etcdLb γ σ`, from 3d's
`adminPost` at the member's recorded auth states, which the member's auth store relates to the
cluster's tables: 2c/3d's invariant), so that `kvServer.Compact` can fire W0's compact denial;
was only "one of four errors", which justified no answer.
Recheck RR2: the denial is `adminDenied σ who tls e`, at the principal the check read: `who`, none
(the flag read off by `AuthInfoFromCtx`, on by `IsAdminPermitted`), or the certificate's `tls`
(read off, `--client-cert-auth`); was W0's denial at any principal once a table had auth off.

Margin: a `nil` result says nothing (the check is at a possibly stale auth state).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Api

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

/-- `aa.isPermitted(ctx)`: `nil` (the user has the root role (or auth is off), at the member's auth state), a token refusal
(`ErrInvalidAuthToken`, from `AuthInfoFromCtx`), or a denial at tables the cluster has had
(`adminDenied`, as `who`, none or `tls`, at a state `etcdLb` bounds). -/
def AuthAdmin.isPermitted.spec : Prop :=
  ∀ (aa s : Loc) (γ : Cluster) (ctx : GoInterface) (who tls : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ authAdminAt aa s γ ∗ Context.ctxOk ctx ∗ reqPrin ctx who tls }}
    (App (Val (aa @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthAdmin.ty @!! go!"isPermitted")) (Val #ctx))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∨ srvErr err .invalidAuthToken ∨
      ∃ (σ : State) (e : EtcdErr), etcdLb γ σ ∗ ⌜adminDenied σ who tls e⌝ ∗ srvErr err e }}

end spec

end V3rpc
end EtcdGrove
end Perennial
