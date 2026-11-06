/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__Apply
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__dispatch

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

theorem apply.uberApplier.Apply.wp_proof
    (hD : apply.uberApplier.dispatch.spec (GF := GF) (hG := hG)) :
    apply.uberApplier.Apply.spec (GF := GF) (hG := hG) := by
  intro E p opts x r rq skip v3 F Pre Q Post rs T U
  wp_start as ⟨#Hu, #Hw, Hown, Hkv, #Hcp, Hwt, Hcs, %Hok, #Hcpr, #Hgp, HLt, HEv, #HGf, Hrv, %Hskip, #HF, HFS, HSp, %Hrr,
    HRO, Hco⟩
  iunfold apply.uberOwn at Hown
  icases Hown with ⟨%a, Ha, #Hs, %HcE, #Hsh⟩
  ihave #Hs' := Hs
  iunfold apply.applierSpec at Hs'
  icases Hs' with ⟨%ai, %Hai, #Ht⟩
  subst Hai
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, -, -, -, -, -, -, -, #HApply, -⟩
  wp_auto
  iapply wp_fupd
  wp_apply HApply $$ %r %rq %skip %v3
      %(methods (go.GoType.PointerType uberApplier.ty) go!"dispatch" #p)
      %(iprop(structFieldRef uberApplier go!"applyV3" p ↦ (GoInterface.ok ai) ∗ apply.kvOwn E x.log ∗
        mvcc.storeWT E.γ ∗ apply.cPre v3 E.P E.f Pre Q Post ∗ E.FS ∗
        (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs ∗ apply.cmpOwn E x.crev ∗
        apply.ltHalf E T ∗ apply.everOwn E U ∗ apply.revokeOwn E rq))
      %(fun ar => iprop(E.FS ∗
        apply.cmpOwn E (apply.dispatchCrev x.chain rq v3 x.crev) ∗ ∃ (a' : GoInterface) (c' : apply.Chain) (o : apply.Outcome),
        structFieldRef uberApplier go!"applyV3" p ↦ a' ∗ apply.applierSpec E c' a' ∗
        apply.kvOwn E (o.logAfter x.log) ∗
        apply.ltHalf E (apply.revokeIds rq v3 o (apply.grantIds rq v3 o T)) ∗
        apply.everOwn E (apply.grantIds rq v3 o U) ∗ apply.revokeOwn E rq ∗
        (∃ t : w64, ⌜apply.grantTTLOk rq t⌝ ∗ E.RO (apply.revokeRest T rq v3 o
          (apply.grantRest t rq v3 o (apply.restAfter rq v3 rs)))) ∗
        ⌜apply.grantOutOk x.chain rq v3 T o⌝ ∗ apply.cPost v3 Pre Post ∗
        ⌜apply.dispatchStep x.chain rq v3 x.log o ∧ apply.chainAfter rq v3 x.chain c' ∧
          apply.kvFloorOk rq v3 F x.log o ∧ a' = GoInterface.ok ai ∧ c' = x.chain⌝ ∗
        (∀ _ : v3 = true, apply.chainClass E.authMode (apply.principalOf rq) x.chain rq o) ∗
        apply.grantRes E rq o ar ∗ apply.revokeAnsR E rq ar ∗ apply.resTrace ar ∗ apply.dispatchResult rq v3 x.log skip ar o))
      [Ha Hkv Hwt Hcs HFS HSp HRO Hco HLt HEv Hrv] as %ar Hpost
  · iframe Hw Ha Hkv Hwt Hcs HFS HSp HRO Hco HLt HEv Hrv
    isplitr
    · iapply apply.rdLend_kvOwn
    imodintro
    iintro %Φ' ⟨Hres, Ha, Hkv, Hwt, Hcs, HFS, HSp, HRO, Hco, HLt, HEv, Hrv⟩ HΦ'
    iapply (hD E p opts x.chain (.ok ai) r rq skip v3 x.log F Pre Q Post rs (apply.principalOf rq) x.crev T U) $$ [Hres Ha Hkv Hwt Hcs HFS HSp HRO Hco HLt HEv Hrv]
    · iframe #
      iframe Hres Ha Hkv Hwt Hcs HFS HSp HRO Hco HLt HEv Hrv
      ipureintro; exact ⟨Hok, HcE, Hrr⟩
    inext
    iintro %ar ⟨Hres, HFS, Hco, HB⟩
    iapply HΦ'
    simp only []
    iframe Hres HFS Hco
    iexact HB
  icases Hpost with (⟨⟨HFS, Hco, %a', %c', %o, Ha', #Hs'', Hkv, HLt, HEv, Hrv, HRO, %Hgo, HPP, %Hst, #Hcls, Hgr, Hvr, Htr, Hres⟩, #Hadm⟩ | ⟨%Hna, ⟨Ha, Hkv, -, Hcs, HFS, -, HRO, Hco, HLt, HEv, Hrv⟩, Hrej⟩)
  · obtain ⟨-, -, -, ha, hc⟩ := id Hst
    subst ha hc
    imodintro
    iapply HΦ
    iframe HFS
    iexists ⟨o.logAfter x.log, x.chain, apply.dispatchCrev x.chain rq v3 x.crev⟩, (.dispatched o skip)
    simp only [apply.applyResultIs, apply.restOut, apply.applyAuthRes, apply.grantIdsA,
      apply.grantRestA, apply.grantResA, apply.grantOutOkA, apply.revokeIdsA, apply.revokeRestA,
      apply.revokeAnsRA]
    iframe Hkv HLt HEv Hrv HPP Hres Htr HRO Hcls Hadm Hco Hgr Hvr %Hgo
    isplitl [Ha']
    · iunfold apply.uberOwn; iexists _; iframe Ha' Hs'' Hsh
      ipureintro; exact HcE
    ipureintro
    exact ⟨⟨Hskip, Hst.1, rfl, Hst.2.1, rfl⟩, Or.inr ⟨o, rfl⟩, Hst.2.2.1⟩
  · iunfold apply.rejectResultIs at Hrej
    icases Hrej with ⟨%Harn, %v, Hv, %Hvf, #HeI⟩
    ipersist Hv
    imodintro
    iapply HΦ
    iframe HFS
    iexists x, .rejected
    simp only [apply.grantIdsA, apply.grantRestA, apply.grantResA, apply.restOut, apply.revokeIdsA,
      apply.revokeRestA, apply.revokeAnsRA]
    iframe Hkv HLt HEv Hrv Hco
    isplitl [Ha]
    · iunfold apply.uberOwn; iexists _; iframe Ha Hs Hsh; ipureintro; exact HcE
    isplitl [Hcs]
    · iapply apply.cPost_of_pre
      iapply apply.cPre_pre
      iexact Hcs
    isplitl [HRO]
    · iexists (apply.grantTTLW rq)
      isplitr
      · ipureintro; exact apply.grantTTLOk_w rq
      iexact HRO
    isplitr
    · ipureintro; simp [apply.grantOutOkA]
    isplitr
    · ipureintro; refine ⟨⟨Hna, rfl⟩, ?_, ?_⟩ <;> simp [apply.applyFloorOk]
    isplitl []
    · iapply apply.resTrace_err ar v Hvf.1 $$ Hv
    isplitl []
    · itrivial
    isplitl []
    · itrivial
    isplitr []
    · simp only [apply.applyResultIs]
      iunfold apply.rejectedResultIs
      isplitr
      · ipureintro; exact Harn
      iexists v
      iframe Hv HeI
      ipureintro; exact Hvf
    simp only [apply.applyAuthRes]
    itrivial

end proof

end EtcdGrove
end Perennial
