/-
Proof of `Spec/.../membership/RaftCluster__SetBackend.lean`: the field's store and the membership
backend's `MustCreateBackendBuckets`. Lean-first (no Rocq counterpart); D22 receiver epochs, S8c
(2026-10-24); an axiom until 2026-11-22 (prove-ps2-members), now proved on the translated body.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__SetBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.membershipBackend__MustCreateBackendBuckets

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem membership.RaftCluster.SetBackend.wp_proof
    (hMC : schema.membershipBackend.MustCreateBackendBuckets.spec (GF := GF) (hG := hG)) :
    membership.RaftCluster.SetBackend.spec (GF := GF) (hG := hG) := by
  intro c oldbe mbl lg d W Pk qo S r hS hm hmr hc
  wp_start as ⟨Hcb, %Hlg, #Hbe, #Hlgf, #HB, Ho, Hwb, Hrb, %Hr⟩
  obtain ⟨hrm, hrmr, hrc⟩ := Hr
  iunfold clusterBeOn at Hcb
  icases Hcb with ⟨%mbl0, %lg0, %Hlg0, Hfld, -, -⟩
  wp_auto
  wp_apply (hMC mbl d W Pk qo S r hS hm hmr hc hrm hrmr hrc) $$ [$Hpkg2 $Hbe $HB $Ho $Hwb $Hrb]
    as ⟨Ho, Hrb⟩
  (try wp_auto)
  iapply HΦ
  iframe Ho Hrb
  iunfold clusterBeOn
  iexists mbl, lg
  iframe Hfld Hbe Hlgf
  ipureintro; exact Hlg

end proof

end EtcdGrove
end Perennial
