/-
The trust boundary: `membership.RaftCluster.Members` (`api/membership` is names-only: `Members` copies the members under a mutex).
-/
import EtcdGrove.Server.Spec.RaftCluster__Members

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

axiom membership.RaftCluster.Members.wp_proof : membership.RaftCluster.Members.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
