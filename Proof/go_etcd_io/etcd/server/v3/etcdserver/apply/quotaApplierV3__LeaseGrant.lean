/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.quotaApplierV3__LeaseGrant
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Packaging
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.quotaApplierV3.LeaseGrant.wp_proof :
    apply.quotaApplierV3.LeaseGrant.spec (GF := GF) (hG := hG) := by
  intro E c inner p r rq g log T rs Pre Q Post info
  wp_start as ⟨#Hq, #Hin, Hgp⟩
  iunfold apply.grantPre at Hgp
  icases Hgp with ⟨%Hrq, #Hr, #Hgr, #Hmode, HltT, HRO, Hwt, Hpre, #Hsp⟩
  iunfold apply.quotaIs at Hq
  icases Hq with ⟨#Hf, %q, #Hqf, #Hqc⟩
  iunfold apply.isQuota at Hqc
  icases Hqc with ⟨%qi, %Hqi, #HAvail, -⟩
  subst Hqi
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, -, -, #HGrant, -⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  wp_auto
  wp_apply HAvail $$ %_ %r [] as %ok %Hok
  · ipureintro; exact Or.inr (Or.inr rfl)
  subst Hok
  ihave Hres := apply.chainRes_quota_out c p (.ok bi) info $$ Hf Hres
  wp_apply HGrant $$ %r %rq %g %log %T %rs %Pre %Q %Post %info [HltT HRO Hwt Hkv Hres Hcs]
    as %resp %err ⟨%o, Hpost⟩
  · iunfold apply.grantPre
    iframe HltT HRO Hwt Hr Hgr Hmode Hsp
    isplitr
    · ipureintro; exact Hrq
    iunfold apply.mPre
    iframe
  iunfold apply.grantPost at Hpost
  icases Hpost with ⟨Hpm, #HeI, %Hst, Hlt, HRO, Hans⟩
  iunfold apply.mPost at Hpm
  icases Hpm with ⟨Hkv, Hres, HPP⟩
  ihave Hres := apply.chainResAny_quota_in c p (.ok bi) $$ Hf Hres
  rcases err with e | _ <;> wp_auto <;>
  · iapply HΦ
    iexists o
    iunfold apply.grantPost
    iframe HeI Hlt HRO Hans
    isplitl [Hkv Hres HPP]
    · iunfold apply.mPost; iframe
    ipureintro; exact Hst

end proof

end EtcdGrove
end Perennial
