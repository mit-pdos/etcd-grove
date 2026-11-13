/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.quotaApplierV3__LeaseGrant
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas
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
  intro E c inner p r rq g log T rs U Pre Q Post info
  -- `lean`'s proof (the grant triple) with `mPreW`/`mPostW` and `threadTok`
  wp_start as ⟨#Hq, #Hin, Htt, Hgp⟩
  iunfold apply.grantPre at Hgp
  icases Hgp with ⟨%Hrq, #Hr, #Hgr, HltT, HRO, Hpre, #Hsp, HU, HUf⟩
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
  icases apply.mPreW_split_chain _ _ _ _ _ _ _ _ $$ Hpre with ⟨Hm, Hres⟩
  wp_auto
  wp_apply HAvail $$ %_ %r [] as %ok %Hok
  · ipureintro; exact Or.inr (Or.inr rfl)
  subst Hok
  ihave Hres := apply.chainRes_quota_out c p (.ok bi) info $$ Hf Hres
  wp_apply HGrant $$ %r %rq %g %log %T %rs %U %Pre %Q %Post %info [Htt HltT HRO Hm Hres HU HUf]
    as %resp %err ⟨Htt, %o, Hpost⟩
  · iframe Htt
    iunfold apply.grantPre
    iframe HltT HRO Hr Hgr Hsp HU HUf
    isplitr
    · ipureintro; exact Hrq
    iapply apply.mPreW_of_rest
    iframe
  iunfold apply.grantPost at Hpost
  icases Hpost with ⟨Hpm, #HeI, HlE, %Hst, Hlt, HRO, HU, Hans⟩
  iunfold apply.mPostW at Hpm
  icases Hpm with ⟨Hpm, Hrt⟩
  iunfold apply.mPost at Hpm
  icases Hpm with ⟨Hkv, Hres, HPP⟩
  ihave Hres := apply.chainResAny_quota_in c p (.ok bi) $$ Hf Hres
  rcases err with e | _ <;> wp_auto <;>
  · iapply HΦ
    iframe Htt
    iexists o
    iunfold apply.grantPost
    iframe HeI HlE Hlt HRO HU Hans
    isplitl [Hkv Hres HPP Hrt]
    · iunfold apply.mPostW
      iframe Hrt
      iunfold apply.mPost
      iframe
    ipureintro; exact Hst

end proof

end EtcdGrove
end Perennial
