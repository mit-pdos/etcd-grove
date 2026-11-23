/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/treemap/Map__find.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.emirpasic.gods.maps.treemap

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [treemap.Assumptions] [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]

set_option goose.wp.extras true

theorem Map.find.wp_proof : Map.find.spec (GF := GF) := fun tm enc es k => by
  wp_start as Htm
  iunfold isTreeMap at Htm
  icases Htm with ⟨%cmp, %sl, Hm, Hsl, Hcap, #Hcmp, %Hs⟩
  ihave #Hcmp' := Hcmp
  iunfold cmpOk at Hcmp'
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  simp only [List.length_map] at Hlen
  ihave HL : (∃ iv : w64, "i" ∷ i_ptr ↦ iv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ es.length ∧
        ∀ j e, j < sint.nat iv → es[j]? = some e → sint.Z e.1 < sint.Z k⌝ : IProp GF) $$ [i]
  · iexists W64 0; iframe; ipureintro; refine ⟨by decide, by simp, ?_⟩
    intro j e hj; have : sint.nat (W64 0) = 0 := rfl; omega
  wp_for HL
  obtain ⟨hi0, hil, hlt⟩ := Hi
  wp_if_destruct
  · have hlt' : sint.Z iv < sint.Z sl.len := by simpa using Hif
    have hiv : sint.nat iv < es.length := by word
    list_elem es (sint.nat iv) as e
    rw [if_pos ⟨hi0, hlt'⟩]
    have hlk : (es.map (toEntry enc))[(sint.Z iv).toNat]? = some (toEntry enc e) := by
      rw [List.getElem?_map]; simp only [sint.nat] at He_lookup; rw [He_lookup]; rfl
    icases ownSlice_elem_acc (sint.Z iv) (toEntry enc e) sl _ _ hi0 hlk $$ Hsl with ⟨He, Hsl⟩
    wp_auto
    ihave Hsl := Hsl $$ He
    rw [list_set_lookup_self _ _ _ hlk]
    wp_apply Hcmp' as %c %Hc
    have hivn : (sint.Z iv).toNat = sint.nat iv := rfl
    wp_if_destruct
    · -- equal: found
      have hk : k = e.1 := Hc.2.mp rfl
      wp_for_post
      iapply HΦ
      isplitl [Hm Hsl Hcap]
      · iunfold isTreeMap; iexists cmp, sl; iframe Hm Hsl Hcap Hcmp; ipureintro; exact Hs
      ipureintro
      have hidx : idxOf es k = sint.nat iv :=
        idxOf_eq es k _ (by omega) (fun j e' hj he' => hlt j e' hj he')
          (fun e' he' => by rw [He_lookup] at he'; cases he'; rw [hk]; omega)
      refine ⟨by rw [hidx]; word, ?_⟩
      rw [hidx, He_lookup]; simp [hk]
    · have hc0 : c ≠ W64 0 := Hif
      wp_if_destruct
      · -- below: not found
        have hk : sint.Z k < sint.Z e.1 := Hc.1.mp Hif
        wp_for_post
        iapply HΦ
        isplitl [Hm Hsl Hcap]
        · iunfold isTreeMap; iexists cmp, sl; iframe Hm Hsl Hcap Hcmp; ipureintro; exact Hs
        ipureintro
        have hidx : idxOf es k = sint.nat iv :=
          idxOf_eq es k _ (by omega) (fun j e' hj he' => hlt j e' hj he')
            (fun e' he' => by rw [He_lookup] at he'; cases he'; omega)
        refine ⟨by rw [hidx]; word, ?_⟩
        rw [hidx, He_lookup]
        simp only [Option.map_some, Option.some.injEq, Bool.false_eq_true, false_iff]
        intro h; rw [h] at hk; omega
      · -- above: next
        have hne : k ≠ e.1 := fun h => hc0 ((Hc.2).mpr h)
        have hge : ¬ sint.Z k < sint.Z e.1 := fun h => Hif (Hc.1.mpr h)
        have hgt : sint.Z e.1 < sint.Z k := by
          have : sint.Z k ≠ sint.Z e.1 := fun h => hne (BitVec.eq_of_toInt_eq h)
          omega
        wp_for_post
        iframe
        iexists (iv + W64 1)
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        intro j e' hj he'
        by_cases hj' : j < sint.nat iv
        · exact hlt j e' hj' he'
        · have : j = sint.nat iv := by word
          subst this; rw [He_lookup] at he'; cases he'; exact hgt
  · -- the end: not found, at the end
    have hge : sint.Z sl.len ≤ sint.Z iv := by
      have := Hif; simp at this; omega
    have hivl : sint.nat iv = es.length := by word
    iapply HΦ
    isplitl [Hm Hsl Hcap]
    · iunfold isTreeMap; iexists cmp, sl; iframe Hm Hsl Hcap Hcmp; ipureintro; exact Hs
    ipureintro
    have hidx : idxOf es k = sint.nat iv :=
      idxOf_eq es k _ (by omega) (fun j e' hj he' => hlt j e' hj he')
        (fun e' he' => by rw [hivl] at he'; simp at he')
    refine ⟨by rw [hidx]; word, ?_⟩
    rw [hidx, hivl]; simp

end proof

end Perennial.github_com.emirpasic.gods.maps.treemap
