/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__Apply
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__dispatch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas

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
  intro E p opts x r rq skip v3 F Pre Q Post rs
  wp_start as ⟨#Hu, #Hw, Hown, Hkv, #Hcp, %Hok, #Hcpr, %Hskip, #HF, Htt, HFS, HSp, %Hrr, HRO, Hco⟩
  iunfold apply.uberOwn at Hown
  icases Hown with ⟨%a, Ha, #Hs, %HcE, #Hsh⟩
  ihave #Hs' := Hs
  iunfold apply.applierSpec at Hs'
  icases Hs' with ⟨%ai, %Hai, #Ht⟩
  subst Hai
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, -, -, -, -, -, -, #HApply, -⟩
  wp_auto
  iapply wp_fupd
  wp_apply HApply $$ %r %rq %skip %v3
      %(methods (go.GoType.PointerType uberApplier.ty) go!"dispatch" #p)
      %(iprop(structFieldRef uberApplier go!"applyV3" p ↦ (GoInterface.ok ai) ∗
        apply.kvOwnPre v3 E x.log Pre Q Post ∗ threadTok ∗ E.FS ∗
        (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs ∗ apply.cmpOwn E x.crev))
      %(fun ar => iprop(threadTok ∗ (∃ B : mvcc.api.BkRef, apply.bkRT B) ∗ E.FS ∗
        E.RO (apply.restAfter rq v3 rs) ∗
        apply.cmpOwn E (apply.dispatchCrev x.chain rq v3 x.crev) ∗ ∃ (a' : GoInterface) (c' : apply.Chain) (o : apply.Outcome),
        structFieldRef uberApplier go!"applyV3" p ↦ a' ∗ apply.applierSpec E c' a' ∗
        apply.kvOwn E (o.logAfter x.log) ∗ apply.cPost v3 Pre Post ∗
        ⌜apply.dispatchStep x.chain rq v3 x.log o ∧ apply.chainAfter rq v3 x.chain c' ∧
          apply.kvFloorOk rq v3 F x.log o ∧ a' = GoInterface.ok ai ∧ c' = x.chain⌝ ∗
        (∀ _ : v3 = true, apply.chainClass E.authMode (apply.principalOf rq) x.chain rq o) ∗
        apply.resTrace ar ∗ apply.dispatchResult rq v3 x.log skip ar o))
      [Ha Hkv Htt HFS HSp HRO Hco] as %ar Hpost
  · iframe Hw Ha Hkv Htt HFS HSp HRO Hco
    isplitr
    · iapply apply.rdLend_kvOwnPre
    imodintro
    iintro %Φ' ⟨Hres, Ha, Hkv, Htt, HFS, HSp, HRO, Hco⟩ HΦ'
    iapply (hD E p opts x.chain (.ok ai) r rq skip v3 x.log F Pre Q Post rs (apply.principalOf rq) x.crev) $$ [Hres Ha Hkv Htt HFS HSp HRO Hco]
    · iframe #
      iframe Hres Ha Hkv Htt HFS HSp HRO Hco
      ipureintro; exact ⟨Hok, HcE, Hrr⟩
    inext
    iintro %ar ⟨Htt, Hrt, Hres, HFS, HRO, Hco, HB⟩
    iapply HΦ'
    simp only []
    iframe Htt Hrt Hres HFS HRO Hco
    iexact HB
  icases Hpost with (⟨⟨Htt, Hrt, HFS, HRO, Hco, %a', %c', %o, Ha', #Hs'', Hkv, HPP, %Hst, #Hcls, Htr, Hres⟩, #Hadm⟩ | ⟨%Hna, ⟨Ha, Hkv, Htt, HFS, -, HRO, Hco⟩, Hrej⟩)
  · obtain ⟨-, -, -, ha, hc⟩ := id Hst
    subst ha hc
    imodintro
    iapply HΦ
    iframe Htt Hrt HFS
    iexists ⟨o.logAfter x.log, x.chain, apply.dispatchCrev x.chain rq v3 x.crev⟩, (.dispatched o skip)
    simp only [apply.applyResultIs, apply.restOut, apply.applyAuthRes]
    iframe Hkv HPP Hres Htr HRO Hcls Hadm Hco
    isplitl [Ha']
    · iunfold apply.uberOwn; iexists _; iframe Ha' Hs'' Hsh
      ipureintro; exact HcE
    ipureintro
    exact ⟨⟨Hskip, Hst.1, rfl, Hst.2.1, rfl⟩, Or.inr ⟨o, rfl⟩, Hst.2.2.1⟩
  · iunfold apply.rejectResultIs at Hrej
    icases Hrej with ⟨%Harn, %v, Hv, %Hvf, #HeI⟩
    ipersist Hv
    ihave ⟨Hkv, Hrt, HPre⟩ := apply.kvOwnPre_kvOwn v3 E x.log Pre Q Post $$ Hkv
    imodintro
    iapply HΦ
    iframe Htt Hrt HFS
    ihave HRO : iprop(E.RO (apply.restOut rq v3 .rejected rs)) $$ [HRO]
    · rw [show apply.restOut rq v3 .rejected rs = rs from rfl]; iexact HRO
    iexists x, .rejected
    iframe Hkv HRO Hco
    isplitl [Ha]
    · iunfold apply.uberOwn; iexists _; iframe Ha Hs Hsh; ipureintro; exact HcE
    isplitl [HPre]
    · iapply apply.cPost_of_pre
      iexact HPre
    isplitr
    · ipureintro; exact ⟨⟨Hna, rfl⟩, Or.inl rfl, trivial⟩
    isplitl []
    · iapply apply.resTrace_err ar v Hvf.1 $$ Hv
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
