/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.quotaApplierV3__Put
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Packaging
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WrapLemmas
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

theorem apply.quotaApplierV3.Put.wp_proof :
    apply.quotaApplierV3.Put.spec (GF := GF) (hG := hG) := by
  intro E c inner p r rq o log F Pre Q Post info
  wp_start as ⟨#Hq, #Hin, Hpre, #HF⟩
  iunfold apply.quotaIs at Hq
  icases Hq with ⟨#Hf, %q, #Hqf, #Hqc⟩
  iunfold apply.isQuota at Hqc
  icases Hqc with ⟨%qi, %Hqi, #HAvail, -⟩
  subst Hqi
  ihave Hai : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, #Hev⟩
  icases applyErrVars_noSpace $$ Hev with ⟨%eN, #HeN, #HeI⟩
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨#HPut, -⟩
  iunfold apply.putPre at Hpre
  icases Hpre with ⟨%Hk, #Hcp, #Hr, Hwt, Hm⟩
  ihave #Hcp := apply.certPre_quota E c rq log $$ Hcp
  iunfold apply.mPre at Hm
  icases Hm with ⟨Hkv, Hres, Hcs⟩
  wp_auto
  wp_apply HAvail $$ %_ %r [] as %ok %Hok
  · ipureintro; exact Or.inl rfl
  ihave Hres := apply.chainRes_quota_out c p (.ok bi) info $$ Hf Hres
  wp_apply HPut $$ %r %rq %o %log %F %Pre %Q %Post [Hwt Hkv Hres Hcs] as %resp %trace %err ⟨Hpost, Htrc⟩
  · iunfold apply.putPre
    iunfold apply.mPre
    iframe
    iframe #
    ipureintro; exact Hk
  iunfold apply.kvPostF at Hpost
  icases Hpost with ⟨%oc, %Hst0, HR, Hkv, Hres, HPP, #Hcls⟩
  obtain ⟨Hst, Hfl⟩ := Hst0
  ihave Hres := apply.chainRes_quota_in c p (.ok bi) info $$ Hf Hres
  ihave #Hcls := apply.chainClass_quota E.authMode info c rq oc $$ Hcls
  have hq : apply.quotaChecks (dispatchKind rq) = true := by rw [Hk.2.1]; rfl
  rcases err with e | _
  · -- an error: passed on
    wp_auto
    iapply HΦ
    isplitr [Htrc]
    rotate_left
    · iexact Htrc
    iunfold apply.kvPostF
    iexists oc
    iframe HR Hkv HPP Hres Hcls
    ipureintro
    simp only [apply.chainStep]
    exact ⟨Hst, Hfl⟩

  · -- `err == nil`: the inner applied the put
    ihave %Hap := apply.putAnswerIs_nil log o resp oc $$ HR
    obtain ⟨log', rfl⟩ := Hap
    wp_auto
    cases ok
    · cases Hok
    · wp_auto
      iapply HΦ
      isplitr [Htrc]
      rotate_left
      · iexact Htrc
      iunfold apply.kvPostF
      iexists (.applied log' false)
      iframe HR Hkv HPP Hres Hcls
      ipureintro
      simp only [apply.chainStep]
      exact ⟨Hst, Hfl⟩

end proof

end EtcdGrove
end Perennial
