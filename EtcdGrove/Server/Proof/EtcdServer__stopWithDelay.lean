/-
The trust boundary: `EtcdServer.stopWithDelay` (names-only: it stops the server after a delay).
-/
import EtcdGrove.Server.Spec.EtcdServer__stopWithDelay

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3 go_etcd_io.etcd.pkg.v3 go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

axiom EtcdServer.stopWithDelay.wp_proof : EtcdServer.stopWithDelay.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
