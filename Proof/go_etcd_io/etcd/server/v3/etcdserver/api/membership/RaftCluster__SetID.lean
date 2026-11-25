/-
Proof of `Spec/.../membership/RaftCluster__SetID.lean` (claim #34, stage 2, 2026-11-25): the two
stores, then `buildMembershipMetric`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__SetID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__buildMembershipMetric

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem membership.RaftCluster.SetID.wp_proof
    (hBMM : membership.RaftCluster.buildMembershipMetric.spec (GF := GF) (hG := hG)) :
    membership.RaftCluster.SetID.spec (GF := GF) (hG := hG) := by
  intro c lid cid lid0 cid0 dq2 dq3 dq4 dq5 mp rp ms rm
  wp_start as ⟨Hlid, Hcid, Hmf, Hmp, Hrf, Hrp⟩
  wp_auto
  wp_apply (hBMM c lid (DFrac.own 1) dq2 dq3 dq4 dq5 mp rp ms rm)
    $$ [$Hpkg $Hlid $Hmf $Hmp $Hrf $Hrp] as ⟨Hlid, Hmf, Hmp, Hrf, Hrp⟩
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
