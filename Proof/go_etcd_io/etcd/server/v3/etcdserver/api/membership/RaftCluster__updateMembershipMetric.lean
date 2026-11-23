/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__updateMembershipMetric.lean`,
over the real body (prove-ps2-metrics, 2026-11-22: until then the trust-boundary axiom, D43 M4): with a
non-zero local id, `knownPeers.WithLabelValues(c.localID.String(), peer.String()).Set(v)`, over
`WithLabelValues`' spec (the vector's label names in `membershipInit`; the ids' hexadecimal strings
are ASCII), whose gauge is a `*gauge` (`metric.isGauge`), and the gauge's proved `Set`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__updateMembershipMetric
public import Spec.go_etcd_io.etcd.client.pkg.v3.types.ID__String_ptr
public import Spec.github_com.prometheus.client_golang.prometheus.GaugeVec__WithLabelValues
public import Spec.github_com.prometheus.client_golang.prometheus.gauge__Set
public import Proof.go_etcd_io.etcd.client.pkg.v3.types.IDStr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem membership.RaftCluster.updateMembershipMetric.wp_proof
    (hIDStringPtr : types.ID.String_ptr.spec (GF := GF) (hG := hG))
    (hWLV : prometheus.GaugeVec.WithLabelValues.spec (GF := GF) (hG := hG))
    (hSet : prometheus.gauge.Set.spec (GF := GF) (hG := hG)) :
    membership.RaftCluster.updateMembershipMetric.spec (GF := GF) (hG := hG) := by
  intro c lid peer known
  wp_start as #Hlid
  ihave Hmi : (go_etcd_io.etcd.server.v3.etcdserver.api.membership.membershipInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, ⟨%vKP, #HKP, %HKPl⟩⟩
  ihave #Hprom : isPkgInit (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus $$ []
  · iPkgInit
  wp_auto
  wp_if_destruct
  · iapply HΦ
    try itrivial
  cases known
  all_goals
    try wp_auto
    wp_apply hIDStringPtr _ DFrac.discard lid $$ [$Hlid] as %ls ⟨-, %Hls⟩
    wp_apply hIDStringPtr $$ [$peer] as %ps ⟨peer, %Hps⟩
    wp_apply wp_slice_literal (V := GoString) [ls, ps]
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hlsl, -⟩
    try wp_auto
    wp_apply hWLV vKP _ [go!"Local", go!"Remote"] [ls, ps] _ $$ [$Hlsl] as %g ⟨%gi, %Hgi, -, #HgR, -⟩
    · iframe #
      ipureintro
      refine ⟨HKPl, by simp, fun v hv => ?_⟩
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl
      · exact utf8Valid_of_ascii _ (Hls ▸ types.idStr_ascii _)
      · exact utf8Valid_of_ascii _ (Hps ▸ types.idStr_ascii _)
    subst Hgi
    iunfold EtcdGrove.prometheus.metric.isGauge at HgR
    icases HgR with ⟨%l, %Hl, #Hcell⟩
    subst Hl
    try wp_auto
    wp_apply hSet $$ [$Hcell]
    try wp_auto
    iapply HΦ
    try itrivial

end proof

end EtcdGrove
end Perennial
