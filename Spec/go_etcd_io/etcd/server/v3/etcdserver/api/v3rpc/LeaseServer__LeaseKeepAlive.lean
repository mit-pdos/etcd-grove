/-
`v3rpc.LeaseServer.LeaseKeepAlive` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Lease/LeaseKeepAlive` (`_Lease_LeaseKeepAlive_Handler`, 3h); 1c's `remoteLeaseAt_keepAlive`, `kaSendAt`, `kaRecvAt` (`examples/specreq/clientv3lease/session.go`).

Proof sketch: a buffered channel; `go` the loop (`leaseKeepAlive.spec`, both halves handed to it; its token from `Fork`); a `select` on the channel and the stream context's `Done` (W0's `Context.Done`/`doneRecv`): the loop's error, or the context's `Err()` (a context's error, or `ErrGRPCNoLeader` from the stream interceptor's `cancellableContext`). The end's facts are `True` (`kaSpec`), so `streamOut`'s second way.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/LeaseServer__LeaseKeepAlive.lean`.

Margin: none.
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

/-- `ls.LeaseKeepAlive(stream)`: a run of the keep-alive stream. -/
def LeaseServer.LeaseKeepAlive.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster) (st ctx : GoInterface) (g : StreamName) (md : MD),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ leaseServerAt p s γ ∗ threadTok ∗ rpcCtx ctx md ∗ srvCtxOf st ctx md ∗
      srvRecv st g (kaSpec γ) md 0 ∗ srvSend st g (kaSpec γ) md 0 }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseKeepAlive")) (Val #st))
  {{ (err : GoInterface), RET #err; threadTok ∗ streamOut st g (kaSpec γ) md err }}

end spec

end V3rpc
end EtcdGrove
end Perennial
