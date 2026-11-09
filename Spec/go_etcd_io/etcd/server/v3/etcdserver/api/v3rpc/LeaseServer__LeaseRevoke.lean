/-
`LeaseServer.LeaseRevoke` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Lease/LeaseRevoke` (the generated `_Lease_LeaseRevoke_Handler`, 3h,
registered by `v3rpc.Server`); 1c's `RemoteCallTriple` for the lease RPCs through grpc and the stub (`examples/specreq/clientv3lease/`, `examples/specreq/v3rpc/lease.go`).

Proof sketch: `ls.le.LeaseRevoke(ctx, r)` (2c's `EtcdServer.LeaseRevoke.spec`, the update passed on, the principal from the contract's `mdPrin`); errors through `togRPCError`; `hdr.fill`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/LeaseServer__LeaseRevoke.lean`: over the contract (was the lease rows' `leaseServerAt` with its own answers).

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

/-- `LeaseServer.LeaseRevoke(ctx, r)` meets the contract of `/etcdserverpb.Lease/LeaseRevoke`. -/
def LeaseServer.LeaseRevoke.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseRevoke")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ leaseServerAt p s γ) (etcdUnary γ go!"/etcdserverpb.Lease/LeaseRevoke") go_etcd_io.etcd.api.v3.etcdserverpb.LeaseRevokeRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.LeaseRevokeResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
