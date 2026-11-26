/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3Capped__Txn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.BackendQuota__Cost
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

theorem apply.applierV3Capped.Txn.wp_proof
    (hCost : storage.BackendQuota.Cost.spec (GF := GF) (hG := hG)) :
    apply.applierV3Capped.Txn.spec (GF := GF) (hG := hG) := by
  intro E c inner p r skip rq t log F Pre Q Post info
  wp_start as ⟨Hc, #Hin, Hpre, #HF, Htt⟩
  iunfold apply.cappedIs at Hc
  ipersist Hc
  ihave Hai : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, #Hev⟩
  icases applyErrVars_noSpace $$ Hev with ⟨%eN, #HeN, #HeI⟩
  wp_auto
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, #HTxn, -⟩
  iunfold apply.txnPre at Hpre
  icases Hpre with ⟨%Hk, #Hr, %T, %Hwt, #Hcp, Hm⟩
  ihave #Hcp := apply.certPreT_capped E c rq log T (by rw [Hk.2.1]; rfl) $$ Hcp
  icases apply.mPreAt_split_chain _ _ _ _ _ _ _ _ _ $$ Hm with ⟨Hm, Hres⟩
  wp_apply hCost
  · iunfold apply.quotaReqOk
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists t; iexact Hr
  iintro %cost -
  wp_auto
  wp_if_destruct
  · -- the request costs: `ErrNoSpace`
    ihave Hm := apply.mPreRest_of_at _ _ _ _ _ _ $$ Hm
    icases apply.mPreRest_reject _ _ _ _ _ $$ Hm with ⟨Hkv, HPre⟩
    ihave Hkv := apply.kvOwn_rejected E log rq .noSpace (by decide) $$ Hkv
    iapply HΦ
    iframe Htt
    isplitl
    rotate_left
    · iapply apply.traceRes_null
    ihave #Hcls : apply.chainClass (GF := GF) E.authMode info (.capped c) rq (.rejected .noSpace) $$ []
    · iapply apply.chainClass_capped_rejected
    ihave #Hlc : apply.chainLeaseClass (GF := GF) E.authMode info (mvcc.leaseItemsOf (mvcc.stateAfter log)) (.capped c) rq (.rejected .noSpace) $$ []
    · iapply apply.chainLeaseClass_capped_rejected
    iunfold apply.kvPostF
    iexists (.rejected .noSpace)
    isplitr
    · ipureintro
      refine ⟨?_, fun _ _ h => by cases h⟩
      simp only [apply.chainStep, apply.cappedRejects, Hk.2.1, ↓reduceIte]
      simp
    simp only [apply.txnAnswerIs, apply.txnOutcomeIs, apply.rejErrIs, apply.Outcome.logAfter]
    iframe Hkv Hres Hcls Hlc
    isplitl []
    · isplitl []
      · ipureintro; trivial
      iunfold txn.errVarIs
      iexists eN
      iframe HeN
      ipureintro; rfl
    iright; iframe HPre; ipureintro
    (first | exact ⟨rfl, trivial⟩ | (simp only [apply.Outcome.logAfter]; exact ⟨rfl, trivial⟩) | simp_all [apply.Outcome.logAfter, apply.revokeIds_rejected, apply.grantRest_rejected, apply.revokeRest_rejected])
  · -- the inner applier's `Txn`
    ihave Hres := apply.chainRes_capped_out c p (.ok bi) info $$ Hc Hres
    wp_apply HTxn $$ %r %skip %rq %t %log %F %Pre %Q %Post [Htt Hm Hres]
      as %resp %trace %err ⟨Hpost, Htrc, Htt⟩
    · iframe Htt
      iunfold apply.txnPre
      iframe #
      isplitr
      · ipureintro; exact Hk
      isplitr
      · ipureintro; exact Hwt
      iapply apply.mPreAt_of_rest
      iframe
    iapply HΦ
    iframe Htt
    isplitr [Htrc]
    rotate_left
    · iexact Htrc
    iunfold apply.kvPostF at Hpost
    iunfold apply.kvPostF
    icases Hpost with ⟨%oc, %Hst0, HR, Hkv, Hres, HPP, #Hcls, #Hlc⟩
    obtain ⟨Hst, Hfl⟩ := Hst0
    ihave #Hcls := apply.chainClass_capped E.authMode info c rq oc $$ Hcls
    ihave #Hlc := apply.chainLeaseClass_capped E.authMode info _ c rq oc $$ Hlc
    iexists oc
    iframe HR Hkv HPP Hcls Hlc
    isplitr
    · ipureintro
      refine ⟨?_, Hfl⟩
      simp only [apply.chainStep, apply.cappedRejects, Hk.2.1, ↓reduceIte]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact Or.inr Hst
    iapply apply.chainRes_capped_in c p (.ok bi) info $$ Hc Hres

end proof

end EtcdGrove
end Perennial
