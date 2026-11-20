/-
`typed.merge`: proved (Prove phase, 2026-11-20): a pooled merging walker set to the two values,
`mergingWalker.merge` at the root (`mergeO_some`: an output), the output wrapped
(`NewValueInterface`), the walker reset and put back (the deferred closure); `merge_mergeO`,
`merge_conforms` give the result's `isTV`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.merge
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.TypeRef__Equals
public import Perennial.Spec.sync.Pool__Get
public import Perennial.Spec.sync.Pool__Put
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__merge
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewFreelistAllocator
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
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

theorem typed.merge.wp_proof
    (h_TypeRef_Equals : schema.TypeRef.Equals.spec (GF := GF))
    (h_sync_Pool_Get : _root_.Perennial.sync.Pool.Get.spec (GF := GF))
    (h_sync_Pool_Put : _root_.Perennial.sync.Pool.Put.spec (GF := GF))
    (h_mergingWalker_merge : typed.mergingWalker.merge.spec (GF := GF))
    (h_NewFreelistAllocator : value.NewFreelistAllocator.spec (GF := GF))
    (h_NewValueInterface : value.NewValueInterface.spec (GF := GF)) :
    typed.merge.spec (GF := GF) := fun lp rp sc S t l r rule postRule => by
  wp_start as ⟨#Hl, #Hr, #Hrule, %Hpost⟩
  subst Hpost
  ihave #HP := typedPkgInit_poolsAt $$ Hpkg
  unfold typedPoolsAt
  icases HP with ⟨-, -, #Pm, -⟩
  icases (isTV_isTVv_law_holds lp sc S t l).mp $$ Hl with ⟨%tvl, #Hlp, #Htvl⟩
  icases (isTV_isTVv_law_holds rp sc S t r).mp $$ Hr with ⟨%tvr, #Hrp, #Htvr⟩
  iunfold isTVv at Htvl Htvr
  icases Htvl with ⟨%Hscl, #Hvl, #Htrl, #HS, %Hcl⟩
  icases Htvr with ⟨%Hscr, #Hvr, #Htrr, -, %Hcr⟩
  ihave ⟨Hlp2, %Hlnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hlp
  ihave ⟨Hrp2, %Hrnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hrp
  iStructNamed Hlp2
  iStructNamed Hrp2
  wp_auto
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  rw [Hscl, Hscr]
  simp only [decide_true, Bool.not_true]
  wp_auto
  ihave #Hotl := (isTypeRefOpt_some_law_holds tvl.typeRef' t).2 $$ Htrl
  ihave #Hotr := (isTypeRefOpt_some_law_holds tvr.typeRef' t).2 $$ Htrr
  wp_apply h_TypeRef_Equals _ _ DFrac.discard DFrac.discard tvl.typeRef' tvr.typeRef' (some t) (some t)
    $$ [] as %b ⟨-, -, %Hb⟩
  · iframe #
  obtain rfl : b = true := Hb.2 rfl
  wp_auto
  wp_apply h_sync_Pool_Get (globalAddr typed.mwPool) typed.mwNewV iprop(True)
    (pooledAs typed.mergingWalker.ty mwPooled) as %x ⟨Hx, -⟩
  · iframe #
  icases Hx with (Hx | %hnil)
  rotate_left
  · exfalso; obtain ⟨h, -⟩ := hnil; simp [typed.mwNewV, func.nil] at h
  iunfold pooledAs at Hx
  icases Hx with ⟨%wl, %hx, Hp⟩
  subst hx
  iunfold mwPooled at Hp
  icases Hp with ⟨%v0, Hw, %Hv0, Hpath, Hsp, Ha⟩
  wp_auto
  simp only
  wp_join iprop(∃ a : value.Allocator, wl ↦ (typed.mergingWalker.mk tvl.value' tvr.value' sc tvl.typeRef'
      v0.path' rule func.nil v0.out' v0.inLeaf' v0.spareWalkers' a) ∗ isAlloc a ∗ mw_ptr ↦ wl)
    at (if: _ then _ else _) with [Hw Ha mw] as ⟨%a, Hw, Ha, mw⟩
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
  obtain ⟨Hout0, Hleaf0⟩ := Hv0
  ihave Hown : mwOwn wl sc S (MWSt.mk tvl.value' tvr.value' t [] none false a) v0.spareWalkers' $$ [Hw Ha Hpath Hsp]
  · unfold mwOwn mwCore
    iexists v0.path'
    iframe
    iexists tvl.typeRef', rule, v0.out'
    rw [← Hleaf0]
    iframe
    iframe #
    unfold outRep
    ipureintro; exact ⟨Hcl.1, Hout0⟩
  wp_apply h_mergingWalker_merge wl sc S (MWSt.mk tvl.value' tvr.value' t [] none false a)
      DFrac.discard DFrac.discard (some l) (some r) func.nil v0.spareWalkers'
    $$ [Hown] as %errs ⟨Herrs, -, -, %sp', Hown, -⟩
  · simp only [isValO]
    iframe; iframe #
    ipureintro
    refine ⟨Or.inl rfl, Hcl.2, Hcr.2, ?_, ?_⟩ <;> trivial
  ihave %Hlen := noErrs_len $$ Herrs
  have hd : ¬ (sint.Z (W64 0) < sint.Z errs.len) := by rw [Hlen]; simp
  rw [decide_eq_false hd]
  simp only
  iunfold mwOwn at Hown
  icases Hown with ⟨%ps', Hcore, Hp', Hsp', Ha'⟩
  iunfold mwCore at Hcore
  icases Hcore with ⟨%tr', %rule', %o', Hw, #Htr', #Hsc', %Hwf', #Hrule', #Ho'⟩
  wp_auto
  have hsome := LawB.mergeO_some_law_holds S t (some l) (some r) Hcl.1 Hcl.2 Hcr.2 (Or.inl rfl)
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hsome
  simp only [hx]
  iunfold outRep at Ho'
  icases Ho' with ⟨%i, #Hoi, #Hi⟩
  ihave ⟨Hoi2, %Honn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hoi
  rw [decide_eq_false Honn]
  wp_auto
  wp_apply h_NewValueInterface i x $$ [] as %v Hv
  · iframe #
  try wp_auto
  simp only
  imod isValF_persist_law_holds _ _ _ $$ Hv with #Hv
  ipersist «$r0»
  wp_apply h_sync_Pool_Put (globalAddr typed.mwPool) typed.mwNewV iprop(True)
      (pooledAs typed.mergingWalker.ty mwPooled) (interface.mkOk (go.GoType.PointerType typed.mergingWalker.ty) #wl)
    $$ [Hw Hp' Hsp' Ha']
  · iframe #
    unfold pooledAs mwPooled
    iexists wl
    isplitr
    · ipureintro; rfl
    iexists _
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iapply (isTV_isTVv_law_holds _ sc S t (merge S t l r)).mpr
  iexists _
  iframe #
  unfold isTVv
  have hm : merge S t l r = x := by rw [merge_mergeO_law_holds, hx]; rfl
  rw [hm]
  iframe #
  ipureintro
  refine ⟨rfl, Hcl.1, ?_⟩
  rw [← hm]
  exact LawB.merge_conforms_law_holds S t l r Hcl.1 Hcl.2 Hcr.2

end proof

end smd
end EtcdGrove
end Perennial
