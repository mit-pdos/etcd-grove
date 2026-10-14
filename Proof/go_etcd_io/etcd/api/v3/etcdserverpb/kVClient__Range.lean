/-
The trust boundary: `(*kVClient).Range` (the generated gRPC stub, names-only: gRPC's `Invoke`,
protobuf's marshalling, the server's generated stub and `grpc.Server`), the server's end-to-end
theorem for `Range` transported to the client (`Wire.lean`).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.kVClient__Range

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

axiom kVClient.Range.wp_proof : kVClient.Range.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
