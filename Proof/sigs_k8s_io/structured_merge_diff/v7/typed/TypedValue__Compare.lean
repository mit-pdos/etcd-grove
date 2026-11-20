/-
`typed.TypedValue.Compare`: proved (Prove phase, 2026-11-20): a pooled compare walker set to the two
values and a fresh comparison (three `NewSet()`), `compareWalker.compare` at the root (its count
premises from `cmpO_card`), the walker reset and put back (the deferred closure); the comparison
handed out (`ownCmp_persist`, `compare_cmpO`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__Compare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.TypeRef__Equals
public import Perennial.Spec.sync.Pool__Get
public import Perennial.Spec.sync.Pool__Put
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__compare
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewFreelistAllocator
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsAPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsB2
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

theorem typed.TypedValue.Compare.wp_proof
    (h_NewSet : fieldpath.NewSet.spec (GF := GF))
    (h_TypeRef_Equals : schema.TypeRef.Equals.spec (GF := GF))
    (h_sync_Pool_Get : _root_.Perennial.sync.Pool.Get.spec (GF := GF))
    (h_sync_Pool_Put : _root_.Perennial.sync.Pool.Put.spec (GF := GF))
    (h_compareWalker_compare : typed.compareWalker.compare.spec (GF := GF))
    (h_NewFreelistAllocator : value.NewFreelistAllocator.spec (GF := GF)) :
    typed.TypedValue.Compare.spec (GF := GF) := fun tv q sc S t l r => by
  wp_start as ⟨#Htvl, #Hq, %Hsz⟩
  ihave #HP := typedPkgInit_poolsAt $$ Hpkg
  unfold typedPoolsAt
  icases HP with ⟨-, -, -, #Pc, -⟩
  icases (isTV_isTVv_law_holds q sc S t r).mp $$ Hq with ⟨%tvr, #Hrp, #Htvr⟩
  iunfold isTVv at Htvl Htvr
  icases Htvl with ⟨%Hscl, #Hvl, #Htrl, #HS, %Hcl⟩
  icases Htvr with ⟨%Hscr, #Hvr, #Htrr, -, %Hcr⟩
  ihave ⟨Hrp2, %Hrnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hrp
  iStructNamed Hrp2
  wp_auto
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  rw [Hscl, Hscr]
  simp only [decide_true, Bool.not_true]
  wp_auto
  iStructNamed lhs
  ihave #Hotl := (isTypeRefOpt_some_law_holds tv.typeRef' t).2 $$ Htrl
  ihave #Hotr := (isTypeRefOpt_some_law_holds tvr.typeRef' t).2 $$ Htrr
  wp_apply h_TypeRef_Equals _ _ (DFrac.own 1) DFrac.discard tv.typeRef' tvr.typeRef' (some t) (some t)
    $$ [typeRef] as %b ⟨typeRef, -, %Hb⟩
  · iframe; iframe #
  obtain rfl : b = true := Hb.2 rfl
  wp_auto
  wp_apply h_sync_Pool_Get (globalAddr typed.cmpwPool) typed.cwNewV iprop(True)
    (pooledAs typed.compareWalker.ty cwPooled) as %x ⟨Hx, -⟩
  · iframe #
  icases Hx with (Hx | %hnil)
  rotate_left
  · exfalso; obtain ⟨h, -⟩ := hnil; simp [typed.cwNewV, func.nil] at h
  iunfold pooledAs at Hx
  icases Hx with ⟨%wl, %hx, Hp⟩
  subst hx
  iunfold cwPooled at Hp
  icases Hp with ⟨%v0, Hw, %Hv0, Hpath, Hsp, Ha⟩
  wp_auto
  simp only
  ihave Hnil := ownSlice_nil (V := GoSlice) (GF := GF) DFrac.discard
  wp_apply (h_NewSet slice.nil DFrac.discard DFrac.discard [] []) $$ [$Hnil] as %s1 ⟨-, -, Hs1⟩
  · unfold isPathsF; itrivial
  ihave Hnil := ownSlice_nil (V := GoSlice) (GF := GF) DFrac.discard
  wp_apply (h_NewSet slice.nil DFrac.discard DFrac.discard [] []) $$ [$Hnil] as %s2 ⟨-, -, Hs2⟩
  · unfold isPathsF; itrivial
  ihave Hnil := ownSlice_nil (V := GoSlice) (GF := GF) DFrac.discard
  wp_apply (h_NewSet slice.nil DFrac.discard DFrac.discard [] []) $$ [$Hnil] as %s3 ⟨-, -, Hs3⟩
  · unfold isPathsF; itrivial
  try wp_auto
  wp_join iprop(∃ a : value.Allocator, wl ↦ (typed.compareWalker.mk tv.value' tvr.value' tv.schema' tv.typeRef'
      v0.path' «$r0_ptr» v0.inLeaf' v0.spareWalkers' a) ∗ isAlloc a ∗ cmpw_ptr ↦ wl)
    at (if: _ then _ else _) with [Hw Ha cmpw] as ⟨%a, Hw, Ha, cmpw⟩
  · icases Ha with (%ha | Ha)
    · rw [ha]
      wp_auto
      wp_apply h_NewFreelistAllocator as %a Ha
      try wp_auto
      wp_join_done
    · icases isAlloc_concrete_law_holds _ $$ Ha with ⟨Ha, Hc⟩
      ihave %hc : ⌜∃ (T : go.GoType) (p : Loc), v0.allocator' = interface.mkOk T #p⌝ $$ [Hc]
      · icases Hc with (⟨%p, %hp⟩ | ⟨%p, %hp⟩)
        · ipureintro; exact ⟨_, p, hp⟩
        · ipureintro; exact ⟨_, p, hp⟩
      obtain ⟨T, p, hp⟩ := hc
      rw [hp]
      wp_auto
      wp_join_done
  have Hleaf0 := Hv0
  have hU : ∀ X : Cmp, Cmp.none.union X = X := fun X => by
    cases X
    simp only [Cmp.union, Cmp.none]
    congr 1 <;> exact LawB.fset_empty_union _
  have hcard := LawB.cmpO_card_law_holds S t [] (some l) (some r) Hsz.1 Hsz.2
  ihave Hown : cwOwn wl sc S (CWSt.mk tv.value' tvr.value' t [] false) «$r0_ptr» Cmp.none v0.spareWalkers'
      $$ [Hw Ha Hpath Hsp «$r0» Hs1 Hs2 Hs3]
  · unfold cwOwn cwCore ownCmp
    iexists v0.path', a
    iframe
    isplitl [Hw]
    · iexists tv.typeRef'
      rw [← Hleaf0, ← Hscl]
      iframe
      iframe #
      ipureintro; exact Hcl.1
    have hE : PathSet.ofList ([] : List Path) = empty := rfl
    simp only [Cmp.none, ← hE]
    isplitl [Hs1]
    · iexact Hs1
    isplitl [Hs2]
    · iexact Hs2
    iexact Hs3
  wp_apply h_compareWalker_compare wl sc S (CWSt.mk tv.value' tvr.value' t [] false) «$r0_ptr» Cmp.none
      DFrac.discard DFrac.discard (some l) (some r) func.nil v0.spareWalkers'
    $$ [Hown] as %errs ⟨Herrs, -, -, %sp', Hown, -⟩
  · simp only [isValO]
    rw [← Hscl]
    iframe; iframe #
    ipureintro
    simp only [hU]
    exact ⟨Or.inl rfl, Hcl.2, Hcr.2, trivial, hcard.1, hcard.2.1, hcard.2.2⟩
  ihave %Hlen := noErrs_len $$ Herrs
  have hd : ¬ (sint.Z (W64 0) < sint.Z errs.len) := by rw [Hlen]; simp
  rw [decide_eq_false hd]
  simp only
  iunfold cwOwn at Hown
  icases Hown with ⟨%ps', %a', Hcore, Hp', Hsp', Ha', Hc⟩
  iunfold cwCore at Hcore
  icases Hcore with ⟨%tr', Hw, #Htr', #Hsc', %Hwf'⟩
  try wp_auto
  simp only
  rw [hU]
  imod ownCmp_persist_law_holds _ _ $$ Hc with #Hc
  wp_apply h_sync_Pool_Put (globalAddr typed.cmpwPool) typed.cwNewV iprop(True)
      (pooledAs typed.compareWalker.ty cwPooled) (interface.mkOk (go.GoType.PointerType typed.compareWalker.ty) #wl)
    $$ [Hw Hp' Hsp' Ha']
  · iframe #
    unfold pooledAs cwPooled
    iexists wl
    isplitr
    · ipureintro; rfl
    iexists _
    iframe
    ipureintro; rfl
  iapply HΦ
  isplitr
  · ipureintro; rfl
  rw [compare_cmpO_law_holds]
  iexact Hc

end proof

end smd
end EtcdGrove
end Perennial
