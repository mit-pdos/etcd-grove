/- Lean-first (no Rocq counterpart). Proof of
`PorcupineDag/Spec/github_com/anishathalye/porcupine/chains__computeFirstUnk.lean`.
-/
module

public import PorcupineDag.Spec.github_com.anishathalye.porcupine.chains__computeFirstUnk
public import PorcupineDag.Spec.github_com.anishathalye.porcupine.Consistency__Check
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.ComputeFirstUnkLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProofMode github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem chains.computeFirstUnk.wp_proof
    (wp_Check : Consistency.Check.spec (GF := GF) (hG := hG)) :
    chains.computeFirstUnk.spec (GF := GF) (hG := hG) := by
  intro ch h cs st c cons hok hwf hshape hfu hheads hc0 hcl hprev
  wp_start as ⟨Hch, #Hlin⟩
  iunfold chainsOwn at Hch
  icases Hch with ⟨%chV, Hch, Hrep⟩
  iunfold chainsRepr at Hrep
  icases Hrep with ⟨%cvs, Hcl, %Hcvs, Hfr, Hcap, Hcls⟩
  obtain ⟨cvc, hcvc⟩ : ∃ cv, cvs[sint.nat c]? = some cv :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  ihave %Hcllen := ownSlice_len $$ Hcl
  icases (ownSlice_halves chV.clients' cvs).1 $$ Hcl with ⟨HclA, HclB⟩
  icases ownSlice_elem_acc (sint.Z c) cvc chV.clients' _ cvs hc0 hcvc $$ HclA with ⟨Hcvc, HclA⟩
  icases (BigSepL.bigSepL_delete_cond (PROP := IProp GF) (Φ := fun k cv => clientOwn h cs st k cv) hcvc).1 $$ Hcls with ⟨Hc, Hrest⟩
  iunfold clientOwn at Hc
  icases Hc with ⟨%Hcvcf, %cosc, Hcosc, %Hcoc, Hfus⟩
  ihave %Hcoslen := ownSlice_len $$ Hcosc
  have hbc : 0 ≤ sint.Z c ∧ sint.Z c < sint.Z chV.clients'.len := ⟨hc0, by have := Hcllen.1; have := Hcvs.1; word⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hch with ⟨Hch, %Hchnn⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hcvc with ⟨Hcvc, %Hcvcnn⟩
  iStructNamedSuffix Hch "_ch"
  iStructNamedSuffix Hcvc "_cc"
  wp_auto
  simp only [hbc, and_self, ↓reduceIte]
  wp_auto
  simp only [hbc, and_self, ↓reduceIte]
  wp_auto
  have hcn : (sint.Z c).toNat = sint.nat c := rfl
  have hcZ : ((sint.nat c : Nat) : Int) = sint.Z c := Int.toNat_of_nonneg hc0
  have hchlen : cosc.length = (chain cs (sint.nat c)).length := Hcoc.1
  have hlenZ : (((chain cs (sint.nat c)).length : Nat) : Int) = sint.Z cvc.cltOps'.len := by
    rw [← hchlen, Hcoslen.1]; exact Int.toNat_of_nonneg Hcoslen.2
  have hhdZ : sint.Z cvc.head' = ((st.head (sint.nat c) : Nat) : Int) := Hcvcf.2.1
  wp_if_destruct
  · -- the head is past the chain: nothing changes
    ihave Hch := typedPointsto_combine _ chV _ Hchnn $$ [clients_ch numOps_ch frontier_ch __ch]
    · simp only [TypedPointsto.typedPointstoDef]; iframe
    ihave Hcvc := typedPointsto_combine _ cvc _ Hcvcnn $$ [id_cc cltOps_cc head_cc nDeps_cc __cc]
    · simp only [TypedPointsto.typedPointstoDef]; iframe
    rw [hcn]
    iapply HΦ
    iexists st
    isplitl
    · iapply (chains_restore ch chV h cs st st cvs (sint.nat c) cvc hcvc Hcvs (fun _ _ _ => rfl))
      rw [hcZ]
      iframe
      unfold clientOwn
      iframe
      ipureintro; exact ⟨Hcvcf, Hcoc⟩
    ipureintro
    refine ⟨rfl, rfl, rfl, hshape, hfu, fun c' k => ?_⟩
    have hn : ¬ (c' = sint.nat c ∧ k = st.head c' ∧ k < (chain cs c').length) := by
      rintro ⟨rfl, rfl, hk⟩; omega
    simp [hn]
  · have hhl : st.head (sint.nat c) < (chain cs (sint.nat c)).length := by omega
    have hhdn : (sint.Z cvc.head').toNat = st.head (sint.nat c) := by omega
    obtain ⟨co, oc, hco, hoc, hcc, hrc, hvc⟩ := coOk_get Hcoc hhl
    have hbh : 0 ≤ sint.Z cvc.head' ∧ sint.Z cvc.head' < sint.Z cvc.cltOps'.len := by omega
    simp only [hbc, and_self, ↓reduceIte]
    wp_auto
    simp only [hbc, and_self, ↓reduceIte]
    rw [← hhdn] at hco
    icases ownSlice_elem_acc (sint.Z cvc.head') co cvc.cltOps' _ cosc hbh.1 hco $$ Hcosc
      with ⟨Hco, Hcosc⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hco with ⟨Hco, %Hconn⟩
    iStructNamedSuffix Hco "_co"
    wp_auto
    simp only [hbh, and_self, ↓reduceIte]
    wp_auto
    ihave Hco := typedPointsto_combine _ co _ Hconn $$ [Op_co globalId_co id_co firstUnk_co visited_co __co]
    · simp only [TypedPointsto.typedPointstoDef]; iframe
    ihave Hcosc := Hcosc $$ %co Hco
    rw [list_set_lookup_self _ _ _ hco]
    cases hcov : co.visited'
    case true =>
      -- already visited: nothing changes
      wp_auto
      ihave Hch := typedPointsto_combine _ chV _ Hchnn $$ [clients_ch numOps_ch frontier_ch __ch]
      · simp only [TypedPointsto.typedPointstoDef]; iframe
      ihave Hcvc := typedPointsto_combine _ cvc _ Hcvcnn $$ [id_cc cltOps_cc head_cc nDeps_cc __cc]
      · simp only [TypedPointsto.typedPointstoDef]; iframe
      rw [hcn]
      iapply HΦ
      iexists st
      isplitl
      · iapply (chains_restore ch chV h cs st st cvs (sint.nat c) cvc hcvc Hcvs (fun _ _ _ => rfl))
        rw [hcZ]
        iframe
        unfold clientOwn
        iframe
        ipureintro; exact ⟨Hcvcf, Hcoc⟩
      ipureintro
      refine ⟨rfl, rfl, rfl, hshape, hfu, fun c' k => ?_⟩
      by_cases hn : c' = sint.nat c ∧ k = st.head c' ∧ k < (chain cs c').length
      · obtain ⟨rfl, rfl, -⟩ := hn
        have : st.visAt (sint.nat c) (st.head (sint.nat c)) = true := by
          rw [← hcov, hvc]; rfl
        simp [this]
      · simp [hn]
    wp_auto
    idx_auto [hbc, hbh]
    sorry

end proof

end porcupine
end EtcdGrove
end Perennial
