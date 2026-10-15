/-
The trust boundary: `EtcdServer.IsMemberExist` (`server.go`, names-only; unit P3b): a call of the
server's `*RaftCluster` (names-only `membership`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__IsMemberExist

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

axiom EtcdServer.IsMemberExist.wp_proof : EtcdServer.IsMemberExist.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
