/-
The trust boundary: `EtcdServer.applyConfChange` (names-only: the membership change (the cluster, raft, the transport) is not translated).
-/
import EtcdGrove.Server.Spec.EtcdServer__applyConfChange

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

axiom EtcdServer.applyConfChange.wp_proof : EtcdServer.applyConfChange.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
