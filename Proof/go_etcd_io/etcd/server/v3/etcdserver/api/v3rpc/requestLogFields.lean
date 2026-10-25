/-
The trust boundary: `v3rpc.requestLogFields` (`v3rpc/interceptor.go`, PR etcd#21401; unit P3b):
constructs `[]zap.Field` slices (`zap.Field.ty` is names-only) from the request's fields covered by
`v3rpc.learnerReqOk req`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.requestLogFields

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

axiom v3rpc.requestLogFields.wp_proof : v3rpc.requestLogFields.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
