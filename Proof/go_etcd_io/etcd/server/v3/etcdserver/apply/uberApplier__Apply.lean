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
  intro E p opts x r rq skip v3 Pre Q Post
  wp_start as ⟨#Hu, #Hw, Hown, Hkv, Hcs, %Hok, %Hskip⟩
  iunfold apply.uberOwn at Hown
  icases Hown with ⟨%a, Ha, #Hs⟩
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
        apply.cPre v3 E.P E.f Pre Q Post))
      %(fun ar => iprop(∃ (a' : GoInterface) (c' : apply.Chain) (o : apply.Outcome),
        structFieldRef uberApplier go!"applyV3" p ↦ a' ∗ apply.applierSpec E c' a' ∗
        apply.kvOwn E (o.logAfter x.log) ∗ apply.cPost v3 Pre Post ∗
        ⌜apply.dispatchStep x.chain rq v3 x.log o ∧ apply.chainAfter rq v3 x.chain c'⌝ ∗
        apply.dispatchResult rq v3 x.log skip ar o))
      [Ha Hkv Hcs] as %ar Hpost
  · iframe Hw Ha Hkv Hcs
    imodintro
    iintro %Φ' ⟨Hres, Ha, Hkv, Hcs⟩ HΦ'
    iapply (hD E p opts x.chain (.ok ai) r rq skip v3 x.log Pre Q Post) $$ [Hres Ha Hkv Hcs]
    · iframe #
      iframe Hres Ha Hkv Hcs
      ipureintro; exact Hok
    inext
    iintro %ar ⟨Hres, HB⟩
    iapply HΦ'
    iframe Hres HB
  icases Hpost with (⟨%a', %c', %o, Ha', #Hs'', Hkv, HPP, %Hst, Hres⟩ | ⟨%Hna, ⟨Ha, Hkv, Hcs⟩, Hrej⟩)
  · imodintro
    iapply HΦ
    iexists ⟨o.logAfter x.log, c'⟩, (.dispatched o skip)
    simp only [apply.applyResultIs]
    iframe Hkv HPP Hres
    isplitl [Ha']
    · iunfold apply.uberOwn; iexists a'; iframe Ha' Hs''
    ipureintro
    exact ⟨⟨Hskip, Hst.1, rfl, Hst.2⟩, Or.inr ⟨o, rfl⟩⟩
  · iunfold apply.rejectResultIs at Hrej
    icases Hrej with ⟨%Harn, %v, Hv, %Hvf⟩
    ipersist Hv
    imodintro
    iapply HΦ
    iexists x, .rejected
    iframe Hkv
    isplitl [Ha]
    · iunfold apply.uberOwn; iexists _; iframe Ha Hs
    isplitl [Hcs]
    · iapply apply.cPost_of_pre
      iapply apply.cPre_pre
      iexact Hcs
    isplitr
    · ipureintro; exact ⟨⟨Hna, rfl⟩, Or.inl rfl⟩
    simp only [apply.applyResultIs]
    iunfold apply.rejectedResultIs
    isplitr
    · ipureintro; exact Harn
    iexists v
    iframe Hv
    ipureintro; exact Hvf

end proof

end EtcdGrove
end Perennial
