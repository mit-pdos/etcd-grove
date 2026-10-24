/-
`Main`'s callees linked (D21 stage M5, 2026-10-19), by hand, as putget's (`putget/MainLinked.lean`):
`putget3.startMember.wp_proof` applied to the server's linked `NewServer` and `Start` and the
server's linked `RaftHandler` (2026-10-24, rafthttp stage 6d; the HTTP boundary's `Serve` the
proof's own) and the trust-boundary axioms of `features.NewDefaultServerFeatureGate` and
`net.Listen`; then `putget3.Main.wp_proof` applied to it, to v3rpc's
and the client's linked results and to the axioms of `zap.NewNop` and `(*grpc.Server).Serve`.
`Results.lean` restates it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget3.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.putget3.startMember
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Link
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Link
public import Proof.go_etcd_io.etcd.client.v3.Link
public import Proof.go_uber_org.zap.NewNop
public import Proof.go_etcd_io.etcd.server.v3.features.NewDefaultServerFeatureGate
public import Proof.net.Listen
public import Proof.google_golang_org.grpc.Server__Serve
public import Perennial.Proof.context.Link

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.putget3.Assumptions]

/-- **`startMember` linked** (see the file header). -/
theorem putget3.wp_startMember [Float64ToInt64Semantics] [ErrorStringLeaf] [ErrorStringNotWriter] :
    putget3.startMember.spec (GF := GF) (hG := hG) :=
  putget3.startMember.wp_proof features.NewDefaultServerFeatureGate.wp_proof wp_NewServer
    EtcdServer.wp_Start net.Listen.wp_proof EtcdServer.wp_RaftHandler

/-- **putget3's `Main` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/putget3/Main.lean`), under the semantic premises of
its callees' linked results (putget's). -/
theorem putget3.wp_Main [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [ErrorStringLeaf]
    [ErrorStringNotWriter] :
    putget3.Main.spec (GF := GF) (hG := hG) :=
  putget3.Main.wp_proof zap.NewNop.wp_proof putget3.wp_startMember v3rpc.wp_Server
    net.Listen.wp_proof grpc.Server.Serve.wp_proof client.v3.clientv3.wp_New context.wp_Background

end results

end EtcdGrove
end Perennial
