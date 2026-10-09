/-
The trust boundary: `zap.Logger.Debug` (`go.uber.org/zap` is names-only).
-/
import EtcdGrove.Server.Spec.zap_Logger__Debug

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

axiom zap.Logger.Debug.wp_proof : zap.Logger.Debug.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
