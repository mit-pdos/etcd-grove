/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Transport__Handler.lean`: `(*rafthttp.Transport).Handler()`, over its
callees' specs (`rafthttp.Transport.Handler_ok`, `TransportSpecs.lean`; rafthttp stage 6f, 2026-10-24).
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__Handler
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newPipelineHandler
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newStreamHandler
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newSnapshotHandler
public import Spec.github_com.xiang90.probing.NewHandler
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__Get
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.pipelineHandler__ServeHTTP
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamHandler__ServeHTTP
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.snapshotHandler__ServeHTTP
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.addRemoteFromRequest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportSpecs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.Transport.Handler.wp_proof
    (hNPH : rafthttp.newPipelineHandler.spec (GF := GF) (hG := hG))
    (hNSH : rafthttp.newStreamHandler.spec (GF := GF) (hG := hG))
    (hNSnH : rafthttp.newSnapshotHandler.spec (GF := GF) (hG := hG))
    (hNewHandler : probing.NewHandler.spec (GF := GF) (hG := hG))
    (hGet : rafthttp.Transport.Get.spec (GF := GF) (hG := hG))
    (hPServe : rafthttp.pipelineHandler.ServeHTTP.spec (GF := GF) (hG := hG))
    (hSServe : rafthttp.streamHandler.ServeHTTP.spec (GF := GF) (hG := hG))
    (hSnServe : rafthttp.snapshotHandler.ServeHTTP.spec (GF := GF) (hG := hG))
    (hARR : rafthttp.addRemoteFromRequest.spec (GF := GF) (hG := hG)) :
    rafthttp.Transport.Handler.spec (GF := GF) (hG := hG) :=
  rafthttp.Transport.Handler_ok hNPH hNSH hNSnH hNewHandler hGet hPServe hSServe hSnServe hARR

end proof

end EtcdGrove
end Perennial
