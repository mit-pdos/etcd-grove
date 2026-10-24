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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.uberApplier.Apply.wp_proof
    (hD : apply.uberApplier.dispatch.spec (GF := GF) (hG := hG)) :
    apply.uberApplier.Apply.spec (GF := GF) (hG := hG) := by
  intro E p opts x r rq skip v3 F Pre Q Post rs
  wp_start as ⟨#Hu, #Hw, Hown, Hkv, #Hcp, Hwt, Hcs, %Hok, %Hskip, #HF, HFS, HSp, HRO⟩
  iunfold apply.uberOwn at Hown
  icases Hown with ⟨%a, Ha, #Hs, %HcE⟩
  ihave #Hs' := Hs
  iunfold apply.applierSpec at Hs'
  icases Hs' with ⟨%ai, %Hai, #Ht⟩
  subst Hai
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, -, -, -, -, -, -, #HApply⟩
  wp_auto
  iapply wp_fupd
  wp_apply HApply $$ %r %rq %skip %v3
      %(methods (go.GoType.PointerType uberApplier.ty) go!"dispatch" #p)
      %(iprop(structFieldRef uberApplier go!"applyV3" p ↦ (GoInterface.ok ai) ∗ apply.kvOwn E x.log ∗
        mvcc.storeWT E.γ ∗ apply.cPre v3 E.P E.f Pre Q Post ∗ E.FS ∗
        (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs))
      %(fun ar => iprop(E.FS ∗ E.RO (apply.restAfter rq v3 rs) ∗ ∃ (a' : GoInterface) (c' : apply.Chain) (o : apply.Outcome),
        structFieldRef uberApplier go!"applyV3" p ↦ a' ∗ apply.applierSpec E c' a' ∗
        apply.kvOwn E (o.logAfter x.log) ∗ apply.cPost v3 Pre Post ∗
        ⌜apply.dispatchStep x.chain rq v3 x.log o ∧ apply.chainAfter rq v3 x.chain c' ∧
          apply.kvFloorOk rq v3 F x.log o⌝ ∗
        (∀ _ : v3 = true, apply.chainClass E.authMode (apply.principalOf rq) x.chain rq o) ∗
        apply.resTrace ar ∗ apply.dispatchResult rq v3 x.log skip ar o))
      [Ha Hkv Hwt Hcs HFS HSp HRO] as %ar Hpost
  · iframe Hw Ha Hkv Hwt Hcs HFS HSp HRO
    imodintro
    iintro %Φ' ⟨Hres, Ha, Hkv, Hwt, Hcs, HFS, HSp, HRO⟩ HΦ'
    iapply (hD E p opts x.chain (.ok ai) r rq skip v3 x.log F Pre Q Post rs (apply.principalOf rq)) $$ [Hres Ha Hkv Hwt Hcs HFS HSp HRO]
    · iframe #
      iframe Hres Ha Hkv Hwt Hcs HFS HSp HRO
      ipureintro; exact ⟨Hok, HcE⟩
    inext
    iintro %ar ⟨Hres, HFS, HRO, HB⟩
    iapply HΦ'
    simp only []
    iframe Hres HFS HRO
    iexact HB
  icases Hpost with (⟨⟨HFS, HRO, %a', %c', %o, Ha', #Hs'', Hkv, HPP, %Hst, #Hcls, Htr, Hres⟩, #Hadm⟩ | ⟨%Hna, ⟨Ha, Hkv, -, Hcs, HFS, -, HRO⟩, Hrej⟩)
  · imodintro
    iapply HΦ
    iframe HFS
    iexists ⟨o.logAfter x.log, c'⟩, (.dispatched o skip)
    simp only [apply.applyResultIs, apply.restOut, apply.applyAuthRes]
    iframe Hkv HPP Hres Htr HRO Hcls Hadm
    isplitl [Ha']
    · iunfold apply.uberOwn; iexists a'; iframe Ha' Hs''
      ipureintro
      rcases Hst.2 with h | ⟨-, -, ns, cr, h⟩ <;> simp [h, HcE]
    ipureintro
    exact ⟨⟨Hskip, Hst.1, rfl, Hst.2.1⟩, Or.inr ⟨o, rfl⟩, Hst.2.2⟩
  · iunfold apply.rejectResultIs at Hrej
    icases Hrej with ⟨%Harn, %v, Hv, %Hvf, #HeI⟩
    ipersist Hv
    imodintro
    iapply HΦ
    iframe HFS
    ihave HRO : iprop(E.RO (apply.restOut rq v3 .rejected rs)) $$ [HRO]
    · rw [show apply.restOut rq v3 .rejected rs = rs from rfl]; iexact HRO
    iexists x, .rejected
    iframe Hkv HRO
    isplitl [Ha]
    · iunfold apply.uberOwn; iexists _; iframe Ha Hs; ipureintro; exact HcE
    isplitl [Hcs]
    · iapply apply.cPost_of_pre
      iapply apply.cPre_pre
      iexact Hcs
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
