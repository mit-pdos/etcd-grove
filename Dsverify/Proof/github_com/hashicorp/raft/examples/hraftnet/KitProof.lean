/-
`Model()` and `Gen` (kit.go), proved over the real code (notes/dsv-hraft.md, S5e): `Model()` meets the
register's porcupine model spec `regS` (`ModelDefs.lean`: `wp_step` and the pure simulation `sim_step`,
`ModelSet.lean`); `Gen` gives the kit's inputs.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ModelDefs
public import Perennial.Proof.github_com.goose_lang.primitive.RandomUint64
public import Perennial.Proof.strconv.Link
public import Proof.strconv.FormatIntDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove EtcdGrove.linkv github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.hashicorp.raft.examples.hraftnet

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
    iapply HΦ'
    unfold regS regRep
    iexists slice.nil, none, []
    isplitr
    · ipureintro
      exact ⟨rfl, sim_init, (fun _ h => by cases h), nofun, Nat.le_refl _⟩
    · rw [List.map_nil]; iapply ownSlice_nil
  isplitr
  · -- Step
    iright
    isplitr
    · ipureintro; exact ⟨trivial, nofun⟩
    unfold stepSpec
    iintro %k %v %s %i %o
    iintro !> %Φ' Hpre HΦ'
    simp only [regS, regS0]
    icases Hpre with ⟨%Hk, Hrep, %Hio⟩
    obtain ⟨⟨x, rfl⟩, u, f, w, rfl⟩ := Hio
    unfold regRep
    icases Hrep with ⟨%sl, %a, %P, %Hr, #Hsl⟩
    obtain ⟨rfl, hsim, ha, hP, hlen⟩ := Hr
    rw [inV_inOf]
    unfold outVal stOf
    wp_auto
    wp_apply (wp_step sl a P (by omega) x u f w) as %ok %s' Hpost
    · iexact Hsl
    rw [← inV_inOf, show (interface.mkOk Out.ty #(Out.mk u f w.1) : GoInterface) = outVal u f w.1
      from rfl]
    have hpm := pM_step regB regDec s _ x _ (regDec_box x u f w)
    obtain ⟨hs1, hs2⟩ := sim_step hsim hP ha x (decAns u f w)
    unfold goStepPost
    icases Hpost with ⟨%Hok, Hpost⟩
    iapply HΦ'
    isplitr
    · iexists sl, a, P
      isplitr
      · ipureintro; exact ⟨rfl, hsim, ha, hP, hlen⟩
      iexact Hsl
    isplitr
    · ipureintro; rw [hpm, hs1, Hok]
    · unfold github_com.anishathalye.porcupine.stepPost
      dsimp only
      rw [hpm]
      cases hst : (pSeq regB).step s (x, decAns u f w) with
      | none => itrivial
      | some S' =>
        dsimp only
        have hsome : ok = true := by rw [Hok, ← hs1, hst]; rfl
        subst hsome
        simp only [ite_true]
        icases Hpost with ⟨%sl', %a', %P', %Hr, #Hsl'⟩
        obtain ⟨rfl, hg⟩ := Hr
        obtain ⟨hP', ha', hl'⟩ := goStep_ok hP ha hg
        iexists sl', a', P'
        isplitr
        · ipureintro; exact ⟨rfl, hs2 a' P' S' hg hst, ha', hP', by omega⟩
        iexact Hsl'
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

/-- `Gen`'s write: a value `"v<c>.<n>"`, short. -/
theorem genPut_ok (id r : w64) :
    HInOk (true, W64 0, [118#8] ++ fmtInt id (W64 10) ++ [46#8] ++
      fmtInt (r / W64 2 % W64 1000000) (W64 10)) := by
  have h1 := EtcdGrove.fmtInt_length_le id (W64 10)
  have h2 := EtcdGrove.fmtInt_length_le (r / W64 2 % W64 1000000) (W64 10)
  refine ⟨by simp only; word, ?_⟩
  simp only [List.length_append, List.length_singleton]
  omega

/-- `Gen`'s read: a way below 3. -/
theorem genGet_ok (r : w64) : HInOk (false, r / W64 2 % W64 3, []) :=
  ⟨by simp only; word, by simp⟩

theorem Gen.wp_proof : Gen.spec (GF := GF) (hG := hG) := by
  unfold Gen.spec EtcdGrove.lintest.genSpec
  iintro #Hinit %id
  wp_start as _
  wp_auto
  wp_apply github_com.goose_lang.primitive.RandomUint64.wp_proof as %r -
  wp_if_destruct
  · wp_apply strconv.wp_Itoa
    wp_apply strconv.wp_Itoa
    iapply HΦ
    imodintro
    ipureintro
    exact ⟨⟨_, genPut_ok id r⟩, rfl⟩
  · iapply HΦ
    imodintro
    ipureintro
    exact ⟨⟨_, genGet_ok r⟩, rfl⟩

end proof

end github_com.hashicorp.raft.examples.hraftnet
end Perennial
