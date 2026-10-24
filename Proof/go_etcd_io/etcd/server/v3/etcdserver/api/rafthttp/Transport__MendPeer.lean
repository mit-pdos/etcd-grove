/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Transport__MendPeer.lean`: `(*rafthttp.Transport).MendPeer(id)`, over its
callees' specs (`rafthttp.Transport.MendPeer_ok`, `TransportSpecs.lean`; rafthttp stage 6f, 2026-10-24).
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__MendPeer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__Resume
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportSpecs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.Transport.MendPeer.wp_proof
    (hM : rafthttp.peer.Resume.spec (GF := GF) (hG := hG)) :
    rafthttp.Transport.MendPeer.spec (GF := GF) (hG := hG) :=
  rafthttp.Transport.MendPeer_ok hM

end proof

end EtcdGrove
end Perennial
