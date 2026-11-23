/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/treemap/Map__Put.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
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

theorem Map.Put.wp_proof (wp_find : Map.find.spec (GF := GF)) : Map.Put.spec (GF := GF) :=
    fun tm enc es k v => by
  wp_start as Htm
  wp_auto
  wp_apply wp_find $$ [$Htm] as %i %found ⟨Htm, %Hi⟩
  iunfold isTreeMap at Htm
  icases Htm with ⟨%cmp, %sl, Hm, Hsl, Hcap, #Hcmp, %Hs⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  simp only [List.length_map] at Hlen
  have hidx := idxOf_le es k
  cases found
  · -- not found: insert
    have hnf : ¬ (es[idxOf es k]?).map Prod.fst = some k := fun h => by
      have := Hi.2.mpr h; cases this
    wp_auto
    wp_apply wp_slice_literal (V := entry) (t := entry.ty) [Perennial.zero_val entry]
    isplitr
    · ipureintro; rfl
    iintro %lptr ⟨Hlit, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hlit] as %s' ⟨Hs', Hcap', -⟩
    ihave %Hl' := ownSlice_len _ _ _ $$ Hs'
    ihave %Hw' := ownSlice_wf _ _ _ $$ Hs'
    simp only [List.length_append, List.length_map, List.length_singleton] at Hl'
    have hb1 : 0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ sint.Z s'.len ∧
        sint.Z s'.len ≤ sint.Z s'.cap := by refine ⟨?_, ?_, Hw'.2⟩ <;> word
    rw [if_pos hb1]
    wp_auto
    have hb2 : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s'.len ∧ sint.Z s'.len ≤ sint.Z s'.cap := by
      refine ⟨?_, ?_, Hw'.2⟩ <;> word
    rw [if_pos hb2]
    wp_auto
    wp_apply wp_slice_copy_within s' _ (i + W64 1) s'.len i s'.len
      ⟨by word, by word, by word⟩ ⟨by word, by word, by word⟩ $$ [$Hs'] as %n ⟨-, Hs'⟩
    have hi1 : sint.nat (i + W64 1) = idxOf es k + 1 := by word
    have hsl : sint.nat s'.len = (es.map (toEntry enc)).length + 1 := by simp; omega
    have hii : sint.nat i = idxOf es k := by word
    rw [hi1, hsl, hii]
    have hb3 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s'.len := ⟨hb2.1, by word⟩
    rw [if_pos hb3]
    wp_apply wp_store_slice_index $$ [$Hs'] as Hs'
    · ipureintro; simp; omega
    have hti : (sint.Z i).toNat = idxOf es k := hii
    rw [hti, insert_shift _ _ _ _ (by simp; omega)]
    iapply HΦ
    iunfold isTreeMap; iexists cmp, s'
    rw [putE_notfound es k v hnf]
    simp only [List.map_append, List.map_take, List.map_cons, List.map_drop]
    have he : toEntry enc (k, v) = entry.mk (enc k) v := rfl
    rw [he]
    iframe Hm Hs' Hcap' Hcmp
    ipureintro
    have := sortedE_putE es k v Hs
    rwa [putE_notfound es k v hnf] at this
  · -- found: replace the entry
    have hf := Hi.2.mp rfl
    have hlt : idxOf es k < es.length := by
      rcases Nat.lt_or_ge (idxOf es k) es.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at hf; cases hf
    have hiv : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := by constructor <;> word
    wp_auto
    rw [if_pos hiv]
    wp_apply wp_store_slice_index $$ [$Hsl] as Hsl
    · ipureintro; simp only [List.length_map]; omega
    iapply HΦ
    iunfold isTreeMap; iexists cmp, sl
    rw [putE_found es k v hf, List.map_set]
    have : (sint.Z i).toNat = idxOf es k := by omega
    rw [this]
    have he : toEntry enc (k, v) = entry.mk (enc k) v := rfl
    rw [he]
    iframe Hm Hsl Hcap Hcmp
    ipureintro
    have := sortedE_putE es k v Hs
    rwa [putE_found es k v hf] at this

end proof

end Perennial.github_com.emirpasic.gods.maps.treemap
