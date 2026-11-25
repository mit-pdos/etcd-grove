/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/newStreamRoundTripper.lean` (rafthttpfix,
2026-11-20; until then a trust-boundary axiom): `transport.NewTimeoutTransport(tlsInfo, dialTimeout, ConnReadTimeout, ConnWriteTimeout)`, the timeouts read from rafthttp's fact, over `NewTimeoutTransport`'s spec.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newStreamRoundTripper
public import Spec.go_etcd_io.etcd.client.pkg.v3.transport.NewTimeoutTransport

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.client.pkg.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.newStreamRoundTripper.wp_proof
    (hNTT : transport.NewTimeoutTransport.spec (GF := GF) (hG := hG)) :
    rafthttp.newStreamRoundTripper.spec (GF := GF) (hG := hG) := by
  intro H tls dt Htls
  wp_start
  ihave #Htp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.transport $$ []
  · iPkgInit
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HCRT, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HCWT⟩
  wp_auto
  wp_apply hNTT H tls dt (W64 5000000000) (W64 5000000000) Htls as %tr %err Hres
  iapply HΦ
  icases Hres with (%Hne | ⟨%He, #Hrt⟩)
  · ileft; ipureintro; exact Hne
  · iright; iframe #; ipureintro; exact He

end proof

end EtcdGrove
end Perennial
