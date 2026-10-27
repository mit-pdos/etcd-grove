/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Transport__Start.lean`: `(*rafthttp.Transport).Start()`, over its
callees' specs (`rafthttp.Transport.Start_ok`, `TransportSpecs.lean`; rafthttp stage 6f, 2026-10-24).
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__Start
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newStreamRoundTripper
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.NewRoundTripper
public import Spec.github_com.xiang90.probing.NewProber
public import Spec.golang_org.x.time.rate.Every
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__Send
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.remote__stop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__SendSnapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__ActiveSince
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

theorem rafthttp.Transport.Start.wp_proof
    (hNSRT : rafthttp.newStreamRoundTripper.spec (GF := GF) (hG := hG))
    (hNRT : rafthttp.NewRoundTripper.spec (GF := GF) (hG := hG))
    (hNewProber : probing.NewProber.spec (GF := GF) (hG := hG))
    (hEvery : rate.Every.spec (GF := GF) (hG := hG))
    (hSend : rafthttp.Transport.Send.spec (GF := GF) (hG := hG))
    (hPeerStop : rafthttp.peer.stop.spec (GF := GF) (hG := hG))
    (hRemoteStop : rafthttp.remote.stop.spec (GF := GF) (hG := hG))
    (hSS : rafthttp.Transport.SendSnapshot.spec (GF := GF) (hG := hG))
    (hAS : rafthttp.Transport.ActiveSince.spec (GF := GF) (hG := hG)) :
    rafthttp.Transport.Start.spec (GF := GF) (hG := hG) :=
  rafthttp.Transport.Start_ok hNSRT hNRT hNewProber hEvery hSend hPeerStop hRemoteStop hSS hAS

end proof

end EtcdGrove
end Perennial
