/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/treemap/Map__Get.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
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

theorem Map.Get.wp_proof (wp_find : Map.find.spec (GF := GF)) : Map.Get.spec (GF := GF) :=
    fun tm enc es k => by
  wp_start as Htm
  wp_auto
  wp_apply wp_find $$ [$Htm] as %i %found ⟨Htm, %Hi⟩
  have hl := lookupE_idx es k
  iunfold isTreeMap at Htm
  icases Htm with ⟨%cmp, %sl, Hm, Hsl, Hcap, #Hcmp, %Hs⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  simp only [List.length_map] at Hlen
  have hidx := idxOf_le es k
  cases found
  · wp_auto
    have : lookupE es k = none := by
      rw [hl Hs]
      rcases h : es[idxOf es k]? with _ | e
      · rfl
      · have : ¬ e.1 = k := by
          intro he; have := Hi.2.mpr (by rw [h]; simp [he]); cases this
        simp [this]
    rw [this]
    simp only [Option.getD_none, Option.isSome_none]
    iapply HΦ
    iunfold isTreeMap; iexists cmp, sl; iframe Hm Hsl Hcap Hcmp
    ipureintro; exact Hs
  · obtain ⟨e, he⟩ : ∃ e, es[idxOf es k]? = some e := by
      rcases h : es[idxOf es k]? with _ | e
      · have := Hi.2.mp rfl; rw [h] at this; cases this
      · exact ⟨e, rfl⟩
    have hek : e.1 = k := by have := Hi.2.mp rfl; rw [he] at this; simpa using this
    have hiv : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := by
      have : idxOf es k < es.length := by
        rcases Nat.lt_or_ge (idxOf es k) es.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at he; cases he
      constructor <;> word
    wp_auto
    rw [if_pos hiv]
    have hlk : (es.map (toEntry enc))[(sint.Z i).toNat]? = some (toEntry enc e) := by
      rw [List.getElem?_map, Hi.1]; simp [he]
    icases ownSlice_elem_acc (sint.Z i) (toEntry enc e) sl _ _ hiv.1 hlk $$ Hsl with ⟨He, Hsl⟩
    wp_auto
    ihave Hsl := Hsl $$ He
    rw [list_set_lookup_self _ _ _ hlk]
    have : lookupE es k = some e.2 := by rw [hl Hs, he]; simp [hek]
    rw [this]
    simp only [Option.getD_some, Option.isSome_some]
    iapply HΦ
    iunfold isTreeMap; iexists cmp, sl; iframe Hm Hsl Hcap Hcmp
    ipureintro; exact Hs

end proof

end Perennial.github_com.emirpasic.gods.maps.treemap
