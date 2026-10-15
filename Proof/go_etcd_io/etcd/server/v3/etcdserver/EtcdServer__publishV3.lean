/-
The trust boundary: `(*EtcdServer).publishV3(timeout)` (`server.go`): names-only, one of the goroutines `Start` attaches.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__publishV3

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

axiom EtcdServer.publishV3.wp_proof : EtcdServer.publishV3.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
