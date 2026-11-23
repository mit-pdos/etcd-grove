/-
`Model()` (kit.go) meets the key-value store's porcupine model spec `kvS` (`Model.spec`,
`ModelDefs.lean`; notes/dsv-craq.md, P2, P4), by `wp_step` and the pure `sim_step` (`ModelSet.lean`).
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.ModelDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.despreston.go_craq.examples.craqnet

open EtcdGrove EtcdGrove.linkv

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.despreston.go_craq.examples.craqnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.despreston.go_craq.examples.craqnet

set_option goose.wp.extras true

theorem Model.wp_proof : Model.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold isModel isEqHash
  simp only
  isplitr
  · ipureintro; trivial
  isplitr
  · -- Init
    unfold initSpec
    iintro !> %Φ' _ HΦ'
    wp_auto
    wp_apply +noauto (wp_map_make1 (K := GoString) (V := GoString) _ _) as %mp Hmp
    iapply fupd_wp
    imod ownMap_persist mp _ _ $$ Hmp with #Hmp
    imodintro
    wp_auto
    iapply HΦ'
    unfold kvS kvRep
    iexists mp, slice.nil, ∅, kvB.init, []
    isplitr
    · ipureintro
      exact ⟨rfl, sim_init, fun _ => rfl, nofun, Nat.le_refl _⟩
    isplitr
    · iexact Hmp
    · rw [List.map_nil]; iapply ownSlice_nil
  isplitr
  · -- Step
    iright
    isplitr
    · ipureintro; exact ⟨trivial, nofun⟩
    unfold stepSpec
    iintro %k %v %s %i %o
    iintro !> %Φ' Hpre HΦ'
    simp only [kvS, kvS0]
    icases Hpre with ⟨%Hk, Hrep, %Hio⟩
    obtain ⟨⟨x, rfl⟩, u, f, w, rfl⟩ := Hio
    unfold kvRep
    icases Hrep with ⟨%mp, %sl, %m, %a, %P, %Hr, #Hm, #Hsl⟩
    obtain ⟨rfl, hsim, hm, hP, hlen⟩ := Hr
    rw [ivK_inOf]
    wp_auto
    wp_apply (wp_step mp sl m a P hm hP (by omega) x u f w) as %ok %s' Hpost
    · isplitl
      · iexact Hm
      · iexact Hsl
    rw [← ivK_inOf]
    have hpm := linkv.pM_step kvB kvDec s _ x _ (kvDec_box x u f w)
    obtain ⟨hs1, hs2⟩ := sim_step hsim x (decAns x u f w)
    unfold stepPost
    icases Hpost with ⟨%Hok, Hpost⟩
    iapply HΦ'
    isplitr
    · iexists mp, sl, m, a, P
      isplitr
      · ipureintro; exact ⟨rfl, hsim, hm, hP, hlen⟩
      isplitr
      · iexact Hm
      · iexact Hsl
    isplitr
    · ipureintro; rw [hpm, hs1, Hok]
    · unfold github_com.anishathalye.porcupine.stepPost
      dsimp only
      rw [hpm]
      cases hst : (pSeq kvB).step s (x, decAns x u f w) with
      | none => itrivial
      | some S' =>
        dsimp only
        have hsome : ok = true := by rw [Hok, ← hs1, hst]; rfl
        subst hsome
        simp only [ite_true]
        icases Hpost with ⟨%mp', %sl', %m', %a', %P', %Hr, #Hm', #Hsl'⟩
        obtain ⟨rfl, hg, hm', hP', hl'⟩ := Hr
        iexists mp', sl', m', a', P'
        isplitr
        · ipureintro; exact ⟨rfl, hs2 a' P' S' hg hst, hm', hP', by omega⟩
        isplitr
        · iexact Hm'
        · iexact Hsl'
  isplitr
  · ipureintro; nofun
  isplitr
  · -- Equal: always false
    unfold equalSpec
    iintro %k %j %v %w %s %t
    iintro !> %Φ' Hpre HΦ'
    wp_auto
    iapply HΦ'
    icases Hpre with ⟨H1, H2⟩
    iframe
    ipureintro; nofun
  ileft
  ipureintro; trivial

end proof

end github_com.despreston.go_craq.examples.craqnet
end Perennial
