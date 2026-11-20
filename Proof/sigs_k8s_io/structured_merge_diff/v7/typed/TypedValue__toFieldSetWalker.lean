/-
`typed.TypedValue.toFieldSetWalker`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__toFieldSetWalker
public import Perennial.Spec.sync.Pool__Get
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewFreelistAllocator

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.LawProofs.Sets

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

theorem typed.TypedValue.toFieldSetWalker.wp_proof
    (h_sync_Pool_Get : _root_.Perennial.sync.Pool.Get.spec (GF := GF))
    (h_NewFreelistAllocator : value.NewFreelistAllocator.spec (GF := GF)) :
    typed.TypedValue.toFieldSetWalker.spec (GF := GF) := fun tv sc S t x => by
  wp_start as Htv
  unfold isTVv
  icases Htv with ⟨%Hs, -, #Htr, #Hsc, %Hwf⟩
  ihave #HP := typedPkgInit_poolsAt $$ Hpkg
  unfold typedPoolsAt
  icases HP with ⟨-, -, -, -, #Pt, -, -⟩
  wp_auto
  wp_apply h_sync_Pool_Get (globalAddr typed.tPool) typed.twNewV iprop(True)
    (pooledAs typed.toFieldSetWalker.ty twPooled) as %y ⟨Hy, -⟩
  · iframe #
  icases Hy with (Hy | %hnil)
  rotate_left
  · exfalso; obtain ⟨h, -⟩ := hnil; simp [typed.twNewV, func.nil] at h
  iunfold pooledAs at Hy
  icases Hy with ⟨%wl, %hy, Hp⟩
  subst hy
  iunfold twPooled at Hp
  icases Hp with ⟨%v0, Hw, %hpath, Hsp⟩
  wp_auto
  wp_apply h_NewFreelistAllocator as %a Ha
  try wp_auto
  iapply HΦ
  iexists _, a, v0.spareWalkers'
  unfold twOwn twCore
  iexists v0.path'
  iframe Hsp Ha
  isplitl [Hw]
  · iexists tv.typeRef'
    rw [← Hs]
    iframe Hw
    iframe #
    ipureintro; exact Hwf.1
  isplitr
  · rw [hpath]; iapply (show ⊢ ownPath (GF := GF) slice.nil [] from ownPath_nil_law_holds)
  iapply (ownSet_empty_law_holds _) $$ «$r0»

end proof

end smd
end EtcdGrove
end Perennial
