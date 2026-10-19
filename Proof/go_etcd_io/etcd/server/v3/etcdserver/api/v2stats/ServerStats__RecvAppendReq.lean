/-
The trust boundary: `(*v2stats.ServerStats).RecvAppendReq()` (names-only).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.ServerStats__RecvAppendReq

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

axiom v2stats.ServerStats.RecvAppendReq.wp_proof : v2stats.ServerStats.RecvAppendReq.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
