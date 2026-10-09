/-
The trust boundary: `apply.Apply` (`server/v3/etcdserver/apply` is names-only: the applier (mvcc, lessor, auth, ...) is not translated).
-/
import EtcdGrove.Server.Spec.apply_Apply

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

axiom apply.Apply.wp_proof : apply.Apply.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
