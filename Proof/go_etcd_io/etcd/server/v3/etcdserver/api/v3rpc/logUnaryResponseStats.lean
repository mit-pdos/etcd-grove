/-
The trust boundary: `v3rpc.logUnaryResponseStats` (`v3rpc/interceptor.go`, PR etcd#21401; unit P3b):
zap's logger (`Debug`, `Warn`) and `zap.Field` slice construction, grpc's `peer.FromContext`, and
protobuf's `proto.Size`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.logUnaryResponseStats

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

axiom v3rpc.logUnaryResponseStats.wp_proof : v3rpc.logUnaryResponseStats.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
