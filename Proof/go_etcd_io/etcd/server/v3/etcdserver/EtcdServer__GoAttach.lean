/-
The trust boundary: `EtcdServer.GoAttach` (names-only; the closure it may run in a goroutine (the apply thread's raises the NOSPACE alarm through raft) is not verified).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__GoAttach

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

axiom EtcdServer.GoAttach.wp_proof : EtcdServer.GoAttach.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
