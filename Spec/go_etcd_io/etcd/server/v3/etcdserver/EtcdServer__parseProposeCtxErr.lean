/-
## `(*EtcdServer).parseProposeCtxErr(err, start)` (internal helper)

Users: `processInternalRaftRequestOnce` (`v3_server.go:1130`), with the proposal context's error.
Mirrors the code: `ErrCanceled` for `Canceled`; for `DeadlineExceeded`, `ErrTimeoutDueToLeaderFail`,
`ErrTimeoutDueToConnectionLost` (the transport's `ActiveSince`, `isConnectedSince`/`
isConnectedToQuorumSince`, 2e's) or `ErrTimeout`; else the error itself. Changes: the old spec's
classification (`applyErrIs`) restated as `srvIndef`. Margin: which of the timeouts is not stated.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A context's error becomes an unsettled server error. -/
def EtcdServer.parseProposeCtxErr.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (err : GoInterface) (start : time.Time),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ threadTok ∗ srvIndef err ∗ srvErrShape err }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"parseProposeCtxErr")) (Val #err)) (Val #start))
  {{ (err' : GoInterface), RET #err'; threadTok ∗ srvIndef err' ∗ srvErrShape err' }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
