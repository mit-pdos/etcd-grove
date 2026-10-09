/-
The trust boundary: `zap.String` (`go.uber.org/zap` is names-only).
-/
module

public import Spec.go_uber_org.zap.String

@[expose] public section

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

axiom zap.String.wp_proof : zap.String.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
