/-
`(*leaseClient).LeaseKeepAlive` (`api/etcdserverpb/rpc_grpc.pb.go`, generated): the streaming stub.

Users: the client's lessor (1c: `recvKeepAliveLoop`'s `resetRecv`, through `remoteLeaseAt`).
Proof sketch: `StaticMethod()`, `append`, the stream descriptor `&Lease_ServiceDesc.Streams[0]`
(`descStreams_init`), the connection's `NewStream` (the caller's `streamStubWP`), the wrapper
`&grpc.GenericClientStream[...]{ClientStream: stream}` on success.
Changes: from `specs-ref/Spec/go_etcd_io/etcd/api/v3/etcdserverpb/leaseClient__LeaseKeepAlive.lean`: over grpc's stream halves (2a) instead of the old `StreamMsg` models; WP form.
Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServerPb

open Iris Iris.BI EtcdModel EtcdWire
open go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

/-- `c.LeaseKeepAlive(ctx, opts...)`: the connection's `NewStream` of `/etcdserverpb.Lease/LeaseKeepAlive`, wrapped (WP
form). -/
def leaseClient.LeaseKeepAlive.spec : Prop :=
  ∀ (c : Loc) (cc ctx : GoInterface) (opts : GoSlice) (dq : DFrac) (os : List GoInterface)
    (Ψ : val → IProp GF),
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗ stubAt etcdserverpb.leaseClient c cc ∗ opts ↦*{dq} os ∗
    (∀ sd : Loc, opts ↦*{dq} os -∗
      streamStubWP (Req := etcdserverpb.LeaseKeepAliveRequest) (Res := etcdserverpb.LeaseKeepAliveResponse) cc sd
        etcdserverpb.Lease_LeaseKeepAlive_FullMethodName etcdserverpb.LeaseKeepAliveRequest.ty etcdserverpb.LeaseKeepAliveResponse.ty ctx os Ψ) ⊢
  WP (App (App (Val (c @!! go.GoType.PointerType etcdserverpb.leaseClient.ty @!! go!"LeaseKeepAlive")) (Val #ctx))
    (Val #opts)) {{ Ψ }}

end spec

end EtcdServerPb
end EtcdGrove
end Perennial
