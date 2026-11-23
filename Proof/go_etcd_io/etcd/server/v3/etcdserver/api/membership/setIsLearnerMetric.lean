/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/setIsLearnerMetric.lean`, over the
real body (prove-ps2-metrics, 2026-11-22: until then the trust-boundary axiom, D43 M5b): it reads
`m.IsLearner` and sets the gauge `isLearner` (`metric.gaugeSetSpec`, in `membershipInit`, from
`NewGauge`'s `metric.isGauge` and the gauge's proved `Set`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.setIsLearnerMetric

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

theorem membership.setIsLearnerMetric.wp_proof :
    membership.setIsLearnerMetric.spec (GF := GF) (hG := hG) := by
  intro m q mm
  wp_start as Hm
  ihave Hmi : (go_etcd_io.etcd.server.v3.etcdserver.api.membership.membershipInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, ⟨%g, #Hg, #HgS⟩, -⟩
  iunfold EtcdGrove.prometheus.metric.gaugeSetSpec at HgS
  iunfold membership.memberAt at Hm
  icases Hm with ⟨%Hmnn, %pu, %cu, Hid, Hpu, Hil, Hnm, Hcu, Hpus, Hcus⟩
  wp_auto
  cases hb : mm.isLearner
  all_goals
    try wp_auto
    wp_apply HgS
    try wp_auto
    iapply HΦ
    iunfold membership.memberAt
    isplitr
    · ipureintro; exact Hmnn
    iexists pu, cu
    rw [hb]
    iframe

end proof

end EtcdGrove
end Perennial
