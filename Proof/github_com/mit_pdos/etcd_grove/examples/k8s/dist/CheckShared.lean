/- Lean-first (no Rocq counterpart).

`CheckShared`'s proof (`Spec/.../k8s/dist/CheckShared.lean`): the loop over the modes, with the mode at
most 2; each mode's model from `Seeded.SharedModel`, checked by `CheckOperationsTimeout`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.dist.CheckShared

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 k8s_etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- Operations that are boxed inputs and outputs naming revisions below `2^62` are `sharedS`'s. -/
theorem opsIoOk_sharedS (g0 : HSt) (R : RevsL) (mode : Nat)
    (ops : List github_com.anishathalye.porcupine.Operation)
    (h : ∀ o ∈ ops, ∃ x y, o.Input' = boxIn x ∧ o.Output' = boxOut y ∧ RevsBelow x y) :
    (emp : IProp GF) ⊢ github_com.anishathalye.porcupine.opsIoOk (sharedS g0 R mode) ops := by
  unfold github_com.anishathalye.porcupine.opsIoOk
  apply BigSepL.bigSepL_intro
  intro k o ho
  obtain ⟨x, y, h1, h2, h3⟩ := h o (List.mem_of_getElem? ho)
  iintro -
  dsimp only [sharedS]
  iexists x, y
  ipureintro
  exact ⟨h1, h2, h3⟩

theorem CheckShared.wp_proof
    (wp_SharedModel : Seeded.SharedModel.spec (GF := GF) (hG := hG))
    (wp_CheckOperationsTimeout : porcupine.CheckOperationsTimeout.spec (GF := GF) (hG := hG)) :
    CheckShared.spec (GF := GF) (hG := hG) := by
  intro _ s hs g0 r R sl ops dur hw hrv hit hR hhist hio
  wp_start as ⟨#Hcc, #Hs0, #Hh0, #Hhs, #Hr, #Hsl⟩
  wp_auto
  ihave HI : (∃ (m : w64), "mode" ∷ mode_ptr ↦ m ∗ "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ 2⌝ : IProp GF)
    $$ [mode]
  · iexists W64 0
    iframe
    ipureintro; refine ⟨by word, by word⟩
  wp_for HI
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_SharedModel s hs g0 r R m $$ [] as %mdl ⟨%Hp, #Hi, %Hsc, #Hs, #Heh⟩
  · iframe #; ipureintro; exact ⟨hw, hrv, hit, hR⟩
  ihave #Hmd : github_com.anishathalye.porcupine.isModel (sharedS g0 R (uint.nat m)) mdl $$ []
  · iapply github_com.anishathalye.porcupine.isModel_of_step
    iframe #
    isplit <;> ipureintro
    · exact Hp
    · exact Hsc
  ihave #Hio : github_com.anishathalye.porcupine.opsIoOk (sharedS (GF := GF) g0 R (uint.nat m)) ops $$ []
  · iapply (opsIoOk_sharedS (GF := GF) (package_sem := package_sem) g0 R (uint.nat m) ops hio)
    iempintro
  wp_apply wp_CheckOperationsTimeout _ (sharedS g0 R (uint.nat m)) mdl sl ops DFrac.discard dur $$ []
    as %res %Hres
  · iframe #; ipureintro; exact hhist
  by_cases hI : res = go!"Illegal"
  · rw [decide_eq_true hI]
    wp_auto
    wp_if_destruct
    · wp_for_post
      iapply HΦ
      ipureintro
      intro _
      refine ⟨rfl, ?_⟩
      rcases Hres with ⟨h, -⟩ | ⟨-, hnL⟩ | ⟨h, -⟩
      · rw [hI] at h; cases h
      · exact hnL
      · rw [hI] at h; cases h
    · rename_i Hif
      wp_for_post
      iframe
      iexists m + W64 1
      iframe
      ipureintro
      have : sint.Z m ≠ 2 := fun h => Hif (by word)
      constructor <;> word
  · rw [decide_eq_false hI]
    wp_auto
    wp_for_post
    iapply HΦ
    ipureintro
    intro h; exact absurd h hI

end proof

end k8s_dist
end EtcdGrove
end Perennial
