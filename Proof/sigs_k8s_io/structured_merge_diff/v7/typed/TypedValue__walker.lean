/-
`typed.TypedValue.walker`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__walker
public import Perennial.Spec.sync.Pool__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewFreelistAllocator

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofs

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

theorem typed.TypedValue.walker.wp_proof
    (h_sync_Pool_Get : _root_.Perennial.sync.Pool.Get.spec (GF := GF))
    (h_NewFreelistAllocator : value.NewFreelistAllocator.spec (GF := GF)) :
    typed.TypedValue.walker.spec (GF := GF) := fun tv S t => by
  wp_start as ⟨#Htr, #Hsc, %Hwf⟩
  ihave #HP := typedPkgInit_poolsAt $$ Hpkg
  unfold typedPoolsAt
  icases HP with ⟨-, -, -, -, -, #Pv, -⟩
  wp_auto
  wp_apply h_sync_Pool_Get (globalAddr typed.vPool) typed.vwNewV iprop(True)
    (pooledAs typed.validatingObjectWalker.ty vwPooled) as %x ⟨Hx, -⟩
  · iframe #
  icases Hx with (Hx | %hnil)
  rotate_left
  · exfalso; obtain ⟨h, -⟩ := hnil; simp [typed.vwNewV, func.nil] at h
  iunfold pooledAs at Hx
  icases Hx with ⟨%wl, %hx, Hp⟩
  subst hx
  iunfold vwPooled at Hp
  icases Hp with ⟨%v0, Hw, Hsp, Ha⟩
  wp_auto
  icases Ha with (%ha | Ha)
  · rw [ha]
    wp_auto
    wp_apply h_NewFreelistAllocator as %a Ha
    try wp_auto
    iapply HΦ
    unfold vwOwn vwCore
    iexists v0.spareWalkers', a
    iframe Hsp Ha
    iexists tv.typeRef'
    iframe Hw
    iframe #
    ipureintro; exact Hwf
  · icases isAlloc_concrete_law_holds _ $$ Ha with ⟨Ha, Hc⟩
    ihave %hc : ⌜∃ (T : go.GoType) (p : Loc), v0.allocator' = interface.mkOk T #p⌝ $$ [Hc]
    · icases Hc with (⟨%p, %hp⟩ | ⟨%p, %hp⟩)
      · ipureintro; exact ⟨_, p, hp⟩
      · ipureintro; exact ⟨_, p, hp⟩
    obtain ⟨T, p, hp⟩ := hc
    rw [hp]
    wp_auto
    iapply HΦ
    unfold vwOwn vwCore
    iexists v0.spareWalkers', _
    iframe Hsp Ha
    iexists tv.typeRef'
    iframe Hw
    iframe #
    ipureintro; exact Hwf

end proof

end smd
end EtcdGrove
end Perennial
