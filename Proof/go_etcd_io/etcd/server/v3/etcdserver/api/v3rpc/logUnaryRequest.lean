/-
The trust boundary: `v3rpc.logUnaryRequest` (`v3rpc/interceptor.go`, PR etcd#21401; unit P3b):
`zap.Field` slice construction (`zap.Field.ty` is names-only) and logger invocation.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.logUnaryRequest

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

axiom v3rpc.logUnaryRequest.wp_proof : v3rpc.logUnaryRequest.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
