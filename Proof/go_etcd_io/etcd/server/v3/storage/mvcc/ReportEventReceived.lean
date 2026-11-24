/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/ReportEventReceived.lean`, over the real body
(prove-ps2-metrics, 2026-11-22: until then the trust-boundary axiom `ReportEventReceived.wp_proof`,
D19j, 2026-10-18): `pendingEventsGauge.Sub(float64(n))` over the gauge's proved `Sub` (the gauge
is the `*gauge` `NewGauge` returns, `metric.isGauge`, in `mvccInit`), and
`totalEventsCounter.Add(float64(n))` over `metric.counterSpec` (`n` is non-negative).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ReportEventReceived
public import Spec.github_com.prometheus.client_golang.prometheus.gauge__Sub

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.ReportEventReceived.wp_proof
    (wp_Sub : prometheus.gauge.Sub.spec (GF := GF) (hG := hG)) :
    mvcc.ReportEventReceived.spec (GF := GF) (hG := hG) := by
  intro n hn
  wp_start as -
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, ⟨%c, #Hc, #HcS⟩, ⟨%g, #Hg, #HgR⟩⟩⟩
  iunfold EtcdGrove.prometheus.metric.isGauge at HgR
  icases HgR with ⟨%l, %Hl, #Hcell⟩
  subst Hl
  ihave #Hprom : isPkgInitSome (PROP := IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_Sub $$ [$Hcell]
  try wp_auto
  iunfold EtcdGrove.prometheus.metric.counterSpec at HcS
  icases HcS with ⟨-, -, #HAdd⟩
  wp_apply HAdd $$ %n %hn
  try wp_auto
  iapply HΦ
  try itrivial

end proof

end EtcdGrove
end Perennial
