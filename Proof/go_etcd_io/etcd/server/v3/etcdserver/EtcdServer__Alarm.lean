/-
The trust boundary: `EtcdServer.Alarm` (`v3_server.go`, names-only; unit P3b). Its body is
`raftRequest` of an `InternalRaftRequest` holding the alarm request, then a type assertion of
the response; `raftRequest` is verified for the request path's put, delete and transaction
requests (`EtcdServer.raftRequest.spec`), whose request predicate (`irrNoHdrIs`) a request built
by `Alarm` would meet with its `Alarm` field only, which no proof here builds.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Alarm

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

axiom EtcdServer.Alarm.wp_proof : EtcdServer.Alarm.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
