/-
`LeaseServer.LeaseLeases` (`server/etcdserver/api/v3rpc/`).

Users: grpc's run of `/etcdserverpb.Lease/LeaseLeases` (the generated `_Lease_LeaseLeases_Handler`, 3h,
registered by `v3rpc.Server`); 1c's `RemoteCallTriple` for the lease RPCs through grpc and the stub (`examples/specreq/clientv3lease/`, `examples/specreq/v3rpc/lease.go`).

Proof sketch: `ls.le.LeaseLeases(ctx, r)` (2c's `EtcdServer.LeaseLeases.spec`, the update passed on, the principal from the contract's `mdPrin`); `ErrLeaseNotFound` (never an answer of the model's `leaseLeases`; an unfired outcome of 2c if any) becomes an empty list, a status that settles nothing is not needed. errors through `togRPCError`; `hdr.fill`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/LeaseServer__LeaseLeases.lean`: over the contract (was the lease rows' `leaseServerAt` with its own answers).

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

/-- `LeaseServer.LeaseLeases(ctx, r)` meets the contract of `/etcdserverpb.Lease/LeaseLeases`. -/
def LeaseServer.LeaseLeases.spec : Prop :=
  ∀ (p s : Loc) (γ : Cluster),
  HandlerTriple (p @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.LeaseServer.ty @!! go!"LeaseLeases")
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗ leaseServerAt p s γ) (etcdUnary γ go!"/etcdserverpb.Lease/LeaseLeases") go_etcd_io.etcd.api.v3.etcdserverpb.LeaseLeasesRequest.ty go_etcd_io.etcd.api.v3.etcdserverpb.LeaseLeasesResponse.ty

end spec

end V3rpc
end EtcdGrove
end Perennial
