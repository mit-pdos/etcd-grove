/-
`Model()` (model.go) meets the store's porcupine model spec `epS` (notes/dsv-epaxos.md):
`State{Config{}}` brackets the initial set (`sim_init`); `Step` is `step` (`wp_step`, `ModelDefs.lean`)
on the decoded operation (`epDec_box`), whose next state brackets the model's next set (`sim_step`);
`Equal` is always false.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.ModelDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet

open EtcdGrove EtcdGrove.linkv github_com.mit_pdos.etcd_grove.examples.lib.remote
  github_com.imdea_software.swiftpaxos_epaxos github_com.imdea_software.swiftpaxos_epaxos.kvs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet.Assumptions]
variable [π : NetProtoGS]
variable [bvi : go.BasicIntoValInj]

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
    wp_bind (App (Val (GoInstruction (CompositeLiteral State.ty))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Config) (t := Config.ty) [zero_val Config]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    iapply fupd_wp
    imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
    imodintro
    wp_auto
    iapply HΦ'
    simp only [epS, epRep]
    iexists _, [(zero_val Config, ([], []))]
    isplitr
    · ipureintro
      refine ⟨rfl, sim_init, fun g hg => ?_⟩
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hg
      subst hg; simp
    isplitr
    · simp only [List.map_cons, List.map_nil]; iexact Hsl
    iapply cfgsRep_single
    unfold cfgRep
    isplitl <;> (simp only [List.map_nil]; iapply ownSlice_nil)
  isplitr
  · -- Step
    iright
    isplitr
    · ipureintro; exact ⟨trivial, nofun⟩
    unfold stepSpec
    iintro %k %v %s %i %o
    iintro !> %Φ' Hpre HΦ'
    simp only [epS, epS0]
    icases Hpre with ⟨%Hk, Hrep, %Hio⟩
    obtain ⟨⟨x, rfl⟩, u, w, rfl⟩ := Hio
    unfold epRep
    icases Hrep with ⟨%sl, %P, %Hr, #Hsl, #HP⟩
    obtain ⟨rfl, hsim, hlen⟩ := Hr
    unfold ivE inV
    wp_auto
    have hP : ∀ g ∈ P.map Prod.snd, g.1.length < 2 ^ 61 ∧ g.2.length < 2 ^ 60 := by
      intro g hg; have := hlen g hg; omega
    wp_apply +noauto wp_step sl P x u w.1 hP $$ [$Hsl $HP] as %ok %r Hr
    icases Hr with ⟨%R, ⟨%HR, %Hok⟩, Hr, #HRc⟩
    iapply fupd_wp
    imod ownSlice_persist _ _ _ $$ Hr with #Hr
    imodintro
    wp_auto
    have hpm := linkv.pM_step epB epDec s _ x _ (epDec_box x u w)
    obtain ⟨hs1, hs2⟩ := sim_step hsim x u w
    iapply HΦ'
    isplitr
    · iexists sl, P
      isplitr
      · ipureintro; exact ⟨rfl, hsim, hlen⟩
      isplitr
      · iexact Hsl
      · iexact HP
    isplitr
    · ipureintro
      unfold ivE inV at hpm
      rw [hpm, hs1, Hok]
    · unfold github_com.anishathalye.porcupine.stepPost
      dsimp only
      unfold ivE inV at hpm
      rw [hpm]
      cases hst : (pSeq epB).step s (x, ansOf u w) with
      | none => itrivial
      | some S' =>
        dsimp only
        iexists r, R
        isplitr
        · ipureintro
          refine ⟨rfl, ?_, ?_⟩
          · rw [HR]; exact hs2 S' hst
          · rw [HR]; exact lenOk_step k _ hlen x u w.1
        isplitr
        · iexact Hr
        · iexact HRc
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

end github_com.imdea_software.swiftpaxos_epaxos.examples.epaxosnet
end Perennial
