/-
`jsoncodec`'s scanner helpers `isDigit`, `scanDigits`, `isHex`, `scanString` against the Lean
scanner (`JsonScan`, `Scan/Def.lean`), and the proof tactics the scanner's proofs share
(`ldidx`, `ldagain`, `fin_ret`). Internal functions (no spec files): their callers in this package
use these lemmas. Ported from dsverify-lab's `examples/vr/proof/VsrProof/Proof/jsoncodec/GoBase.lean`
(lab master 915f964).
-/
module

public import Net.Proof.models_lab.jsoncodec.Base
public import Net.Proof.models_lab.jsoncodec.Scan.NumSteps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

theorem spaceB_spB (c : w8) : spaceB c = JsonScan.spB c := by
  simp [spaceB, JsonScan.spB]

/-- The whitespace run at the start of `l` is `n` long. -/
theorem takeWhile_len (p : w8 → Bool) (l : List w8) (n : Nat) (hn : n ≤ l.length)
    (hsp : ∀ k < n, ∀ x, l[k]? = some x → p x = true)
    (hend : n = l.length ∨ ∃ x, l[n]? = some x ∧ p x = false) :
    (l.takeWhile p).length = n := by
  induction l generalizing n with
  | nil => simp at hn; simp [hn]
  | cons c l ih =>
    cases n with
    | zero =>
      rcases hend with h | ⟨x, hx, hxf⟩
      · simp at h
      · simp at hx; subst hx; simp [List.takeWhile_cons, hxf]
    | succ n =>
      have hc := hsp 0 (by omega) c rfl
      simp only [List.takeWhile_cons, hc, if_true, List.length_cons]
      congr 1
      apply ih n (by simp at hn; omega)
      · intro k hk x hx; exact hsp (k + 1) (by omega) x (by simpa using hx)
      · rcases hend with h | ⟨x, hx, hxf⟩
        · left; simp at h; omega
        · right; exact ⟨x, by simpa using hx, hxf⟩

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true

theorem wp_isDigit (c : w8) :
    {{ (True : IProp GF) }}
      (App (Val (@! models_lab.jsoncodec.isDigit)) (Val #c))
    {{ RET #(JsonScan.isDig c); True }} := by
  wp_start
  wp_auto
  wp_if_destruct
  · have e : JsonScan.isDig c = decide (uint.Z c ≤ uint.Z (W8 57)) := by
      simp only [JsonScan.isDig]; rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, decide_eq_true_eq, BitVec.le_def]
      simp only [uint.Z, W8] at Hif ⊢
      constructor
      · intro h; simp at h ⊢; omega
      · intro h; simp at Hif h ⊢; omega
    rw [e]; iapply HΦ; itrivial
  · have e : JsonScan.isDig c = false := by
      simp only [JsonScan.isDig, Bool.and_eq_false_iff, decide_eq_false_iff_not, BitVec.le_def]
      simp only [uint.Z, W8] at Hif
      left; intro h; apply Hif; simp at h ⊢; omega
    rw [e]; iapply HΦ; itrivial

/-- `scanDigits(b, i)`: the index after the digits at `i`. -/
theorem wp_scanDigits (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (hi : uint.nat i ≤ bs.length) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (App (Val (@! models_lab.jsoncodec.scanDigits)) (Val #b)) (Val #i))
    {{ RET #(W64 ((JsonScan.digitsL (bs.drop (uint.nat i)) (uint.nat i)).1 : Int));
        b ↦*{dq} bs }} := by
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  rw [JsonScan.digitsL_eq]
  wp_auto
  ihave IH : iprop(∃ (n : w64),
      "j" ∷ j_ptr ↦ n ∗
      "%Hn" ∷ ⌜uint.nat i ≤ uint.nat n ∧ uint.nat n ≤ bs.length ∧
        ∀ k < uint.nat n - uint.nat i, ∀ x, (bs.drop (uint.nat i))[k]? = some x →
          JsonScan.isDig x = true⌝) $$ [j]
  · iexists _; iframe; ipureintro; refine ⟨Nat.le_refl _, hi, ?_⟩; intro k hk; omega
  wp_for IH
  wp_if_destruct
  · have Hlt : uint.nat n < bs.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, bs[uint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have hb : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z b.len := by word
    have hnz : (sint.Z n).toNat = uint.nat n := by word
    rw [if_pos hb]
    wp_apply wp_load_slice_index b (sint.Z n) bs dq x hb.1 $$ [Hs] as Hs
    · iframe; ipureintro; rw [hnz]; exact Hx
    wp_apply wp_isDigit x
    by_cases hsp : JsonScan.isDig x = true
    · simp only [hsp, decide_true, ↓reduceIte]
      wp_auto
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro k hk y hy
      by_cases hkn : k < uint.nat n - uint.nat i
      · exact Hn.2.2 k hkn y hy
      · have : k = uint.nat n - uint.nat i := by word
        subst this
        rw [List.getElem?_drop, show uint.nat i + (uint.nat n - uint.nat i) = uint.nat n by omega,
          Hx] at hy
        cases hy; exact hsp
    · simp only [Bool.not_eq_true] at hsp
      simp only [hsp]
      cleanup_bool_decide
      wp_auto
      have := takeWhile_len JsonScan.isDig (bs.drop (uint.nat i)) (uint.nat n - uint.nat i)
        (by simp; omega) Hn.2.2 (Or.inr ⟨x, by rw [List.getElem?_drop,
          show uint.nat i + (uint.nat n - uint.nat i) = uint.nat n by omega]; exact Hx, hsp⟩)
      have e : W64 ((uint.nat i + ((List.drop (uint.nat i) bs).takeWhile JsonScan.isDig).length : Nat) : Int) = n := by
        rw [this]; word
      rw [← e]; iapply HΦ; iframe
  · have hn : uint.nat n = bs.length := by word
    have := takeWhile_len JsonScan.isDig (bs.drop (uint.nat i)) (uint.nat n - uint.nat i)
      (by simp; omega) Hn.2.2 (Or.inl (by simp; omega))
    have e : W64 ((uint.nat i + ((List.drop (uint.nat i) bs).takeWhile JsonScan.isDig).length : Nat) : Int) = n := by
      rw [this]; word
    rw [← e]; iapply HΦ; iframe

theorem bool_finish (Φ : val → IProp GF) (a b : Bool) (h : a = b) :
    (True -∗ Φ #a) ⊢ Φ #b := by
  subst h; iintro H; iapply H; itrivial

theorem wp_isHex (c : w8) :
    {{ (True : IProp GF) }}
      (App (Val (@! models_lab.jsoncodec.isHex)) (Val #c))
    {{ RET #(JsonScan.isHexB c); True }} := by
  wp_start
  wp_auto
  wp_apply wp_isDigit c
  by_cases hd : JsonScan.isDig c = true
  · simp only [hd]
    wp_auto
    have : JsonScan.isHexB c = true := by simp [JsonScan.isHexB, hd]
    rw [this]; iapply HΦ; itrivial
  · simp only [Bool.not_eq_true] at hd
    simp only [hd]
    wp_auto
    have key : JsonScan.isHexB c = Bool.or (decide (97#8 ≤ c) && decide (c ≤ 102#8))
        (decide (65#8 ≤ c) && decide (c ≤ 70#8)) := by simp [JsonScan.isHexB, hd]
    rw [key]
    simp only [uint.Z, W8, BitVec.le_def]
    wp_if_destruct
    · wp_if_destruct
      · iapply bool_finish Φ _ _ ?_ $$ HΦ; simp at *; (try rw [Bool.eq_iff_iff]); (try simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]); omega
      · wp_if_destruct
        · iapply bool_finish Φ _ _ ?_ $$ HΦ; simp at *; (try rw [Bool.eq_iff_iff]); (try simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]); omega
        · iapply bool_finish Φ _ _ ?_ $$ HΦ; simp at *; (try rw [Bool.eq_iff_iff]); (try simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]); omega
    · wp_if_destruct
      · iapply bool_finish Φ _ _ ?_ $$ HΦ; simp at *; (try rw [Bool.eq_iff_iff]); (try simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]); omega
      · iapply bool_finish Φ _ _ ?_ $$ HΦ; simp at *; (try rw [Bool.eq_iff_iff]); (try simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]); omega

theorem pair_finish (Φ : val → IProp GF) (P : IProp GF) (a b a' b' : w64) (h1 : a = a')
    (h2 : b = b') : (P -∗ Φ (PairV #a #b)) ⊢ P -∗ Φ (PairV #a' #b') := by
  subst h1; subst h2; iintro H; iexact H

/-- A slice's length is below `2^63`. -/
theorem len_lt (b : GoSlice) (bs : List w8) (h : bs.length = sint.nat b.len ∧ 0 ≤ sint.Z b.len) :
    bs.length < 2 ^ 63 := by
  have := h.1; word

/-- `scanString(b, i)` (the opening quote at `i`): `strL` after it. -/
theorem wp_scanString (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (hi : uint.nat i < bs.length) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (App (Val (@! models_lab.jsoncodec.scanString)) (Val #b)) (Val #i))
    {{ RET (PairV #(W64 ((JsonScan.strL (bs.drop (uint.nat i + 1)) (uint.nat i + 1)).1 : Int))
          #(W64 ((JsonScan.strL (bs.drop (uint.nat i + 1)) (uint.nat i + 1)).2 : Int)));
        b ↦*{dq} bs }} := by
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := len_lt b bs Hlen
  simp only [models_lab.jsoncodec.Done, models_lab.jsoncodec.More,
    models_lab.jsoncodec.Bad]
  wp_auto
  ihave IH : iprop(∃ (n : w64),
      "j" ∷ j_ptr ↦ n ∗
      "%Hn" ∷ ⌜uint.nat i + 1 ≤ uint.nat n ∧ uint.nat n ≤ bs.length ∧
        JsonScan.strL (bs.drop (uint.nat i + 1)) (uint.nat i + 1) =
          JsonScan.strL (bs.drop (uint.nat n)) (uint.nat n)⌝) $$ [j]
  · iexists _; iframe; ipureintro; refine ⟨by word, by word, by rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word]⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : uint.nat n < bs.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, bs[uint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have hb : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z b.len := by word
    have hnz : (sint.Z n).toNat = uint.nat n := by word
    rw [if_pos hb]
    wp_apply wp_load_slice_index b (sint.Z n) bs dq x hb.1 $$ [Hs] as Hs
    · iframe; ipureintro; rw [hnz]; exact Hx
    have hr := Hn.2.2
    wp_if_destruct
    · wp_for_post
      rw [JsonScan.strL_q bs _ Hx] at hr
      iapply pair_finish Φ _ _ _ _ _ (by rw [hr]; try rfl) (by rw [hr]; try word) $$ HΦ
      iexact Hs
    · have hq : x ≠ 34#8 := by intro h; apply Hif; rw [h]; rfl
      wp_if_destruct
      · have hc : x < 32#8 := by
          simp only [uint.Z, W8] at Hif; simp at Hif; simp [BitVec.lt_def]; omega
        wp_for_post
        rw [JsonScan.strL_ctl bs _ x Hx hq hc] at hr
        iapply pair_finish Φ _ _ _ _ _ (by rw [hr]; try rfl) (by rw [hr]; try word) $$ HΦ
        iexact Hs
      · have hc : ¬ x < 32#8 := by
          simp only [uint.Z, W8] at Hif; simp at Hif; simp [BitVec.lt_def]; omega
        wp_if_destruct
        · have Hx92 : bs[uint.nat n]? = some 92#8 := by rw [Hx]; rfl
          wp_if_destruct
          · wp_for_post
            rw [JsonScan.strL_bs_end bs _ Hx92 (by word)] at hr
            iapply pair_finish Φ _ _ _ _ _ (by rw [hr]; try rfl) (by rw [hr]; try word) $$ HΦ
            iexact Hs
          · have Hlt1 : uint.nat n + 1 < bs.length := by word
            obtain ⟨e, He⟩ : ∃ e, bs[uint.nat n + 1]? = some e := ⟨_, List.getElem?_eq_getElem Hlt1⟩
            have hb1 : 0 ≤ sint.Z (n + W64 1) ∧ sint.Z (n + W64 1) < sint.Z b.len := by word
            have hnz1 : (sint.Z (n + W64 1)).toNat = uint.nat n + 1 := by word
            rw [if_pos hb1]
            wp_apply wp_load_slice_index b _ bs dq e hb1.1 $$ [Hs] as Hs
            · iframe; ipureintro; rw [hnz1]; exact He
            wp_if_destruct
            · have He' : bs[uint.nat n + 1]? = some 117#8 := by rw [He]; rfl
              have hu4 := JsonScan.strL_u bs _ Hx92 He'
              ihave IK : iprop(∃ (kk : w64),
                  "k" ∷ k_ptr ↦ kk ∗
                  "%Hk" ∷ ⌜uint.nat n + 2 ≤ uint.nat kk ∧ uint.nat kk ≤ uint.nat n + 6 ∧
                    uint.nat kk ≤ bs.length ∧
                    JsonScan.strL (bs.drop (uint.nat n)) (uint.nat n) =
                      JsonScan.hexR (uint.nat n + 6 - uint.nat kk) (bs.drop (uint.nat kk))
                        (uint.nat kk)⌝) $$ [k]
              · iexists _; iframe; ipureintro
                refine ⟨by word, by word, by word, ?_⟩
                have hk2 : uint.nat (n + W64 2) = uint.nat n + 2 := by word
                rw [hu4, hk2, show uint.nat n + 6 - (uint.nat n + 2) = 4 by omega]
              wp_for IK
              wp_if_destruct
              · have hm : uint.nat n + 6 - uint.nat kk = (uint.nat n + 6 - uint.nat kk - 1) + 1 := by
                  word
                wp_if_destruct
                · wp_for_post
                  wp_for_post
                  rw [Hk.2.2.2, hm, JsonScan.hexR_end bs _ _ (by word)] at hr
                  iapply pair_finish Φ _ _ _ _ _ (by rw [hr]; try rfl) (by rw [hr]; try word) $$ HΦ
                  iexact Hs
                · have Hltk : uint.nat kk < bs.length := by word
                  obtain ⟨h, Hh⟩ : ∃ h, bs[uint.nat kk]? = some h :=
                    ⟨_, List.getElem?_eq_getElem Hltk⟩
                  have hbk : 0 ≤ sint.Z kk ∧ sint.Z kk < sint.Z b.len := by word
                  have hkz : (sint.Z kk).toNat = uint.nat kk := by word
                  rw [if_pos hbk]
                  wp_apply wp_load_slice_index b _ bs dq h hbk.1 $$ [Hs] as Hs
                  · iframe; ipureintro; rw [hkz]; exact Hh
                  wp_apply wp_isHex h
                  by_cases hh : JsonScan.isHexB h = true
                  · simp only [hh]
                    wp_auto
                    wp_for_post
                    iframe
                    iexists _
                    iframe
                    ipureintro
                    refine ⟨by word, by word, by word, ?_⟩
                    have hk1 : uint.nat (kk + W64 1) = uint.nat kk + 1 := by word
                    rw [Hk.2.2.2, hm, JsonScan.hexR_ok bs _ _ h Hh hh, hk1,
                      show uint.nat n + 6 - (uint.nat kk + 1) = uint.nat n + 6 - uint.nat kk - 1 by omega]
                  · simp only [Bool.not_eq_true] at hh
                    simp only [hh]
                    wp_auto
                    wp_for_post
                    wp_for_post
                    rw [Hk.2.2.2, hm, JsonScan.hexR_bad bs _ _ h Hh hh] at hr
                    iapply pair_finish Φ _ _ _ _ _ (by rw [hr]; try rfl) (by rw [hr]; try word) $$ HΦ
                    iexact Hs
              · have hk6 : uint.nat kk = uint.nat n + 6 := by word
                wp_for_post
                iframe
                iexists _
                iframe
                ipureintro
                refine ⟨by word, by word, ?_⟩
                rw [hr, Hk.2.2.2, hk6, Nat.sub_self]
                simp only [JsonScan.hexR]
            · have hu : e ≠ 117#8 := by intro h; apply Hif; rw [h]; rfl
              by_cases hesc : JsonScan.escB e = true
              · have hs := JsonScan.strL_esc bs _ e Hx92 He hu hesc
                have he8 : e = W8 34 ∨ e = W8 92 ∨ e = W8 47 ∨ e = W8 98 ∨ e = W8 102 ∨
                    e = W8 110 ∨ e = W8 114 ∨ e = W8 116 := by
                  simp only [JsonScan.escB, List.contains_cons, List.contains_nil, Bool.or_false,
                    Bool.or_eq_true, beq_iff_eq] at hesc
                  rcases hesc with h|h|h|h|h|h|h|h <;> subst h <;> decide
                rcases he8 with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
                (wp_auto
                 wp_for_post
                 iframe
                 iexists _
                 iframe
                 ipureintro
                 refine ⟨by word, by word, ?_⟩
                 rw [hr, hs]; congr 2 <;> word)
              · simp only [Bool.not_eq_true] at hesc
                have hs := JsonScan.strL_badesc bs _ e Hx92 He hu hesc
                iterate 8 (wp_if_destruct; (try (exfalso; revert hesc; decide)))
                wp_for_post
                iapply pair_finish Φ _ _ _ _ _ (by rw [hr, hs]; rfl) (by rw [hr, hs]; word) $$ HΦ
                iexact Hs
        · have hbs : x ≠ 92#8 := by intro h; apply Hif; rw [h]; rfl
          wp_for_post
          iframe
          iexists _
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [hr, JsonScan.strL_other bs _ x Hx hq hc hbs]
          congr 2 <;> word
  · have hn : uint.nat n = bs.length := by word
    rw [Hn.2.2, JsonScan.strL_end bs _ (by omega)]
    iapply pair_finish Φ _ _ _ _ _ rfl (by word) $$ HΦ
    iexact Hs

theorem digEnd_le (bs : List w8) (j : Nat) (h : j ≤ bs.length) : JsonScan.digEnd bs j ≤ bs.length := by
  have := (List.takeWhile_prefix JsonScan.isDig (l := bs.drop j)).length_le
  simp [JsonScan.digEnd] at *; omega

theorem digEnd_ge (bs : List w8) (j : Nat) : j ≤ JsonScan.digEnd bs j := by
  simp [JsonScan.digEnd]

set_option hygiene false in
/-- Load `b[j]` (in bounds): its byte `x` with `hx : bs[uint.nat j]? = some x`. -/
macro "ldidx " j:term ", " x:ident ", " hx:ident : tactic => `(tactic| (
  obtain ⟨$x, $hx⟩ : ∃ x, bs[uint.nat $j]? = some x := ⟨_, List.getElem?_eq_getElem (by word)⟩
  rw [if_pos (show 0 ≤ sint.Z $j ∧ sint.Z $j < sint.Z b.len by word)]
  wp_apply wp_load_slice_index b (sint.Z $j) bs dq $x (by word) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z $j).toNat = uint.nat $j by word]; exact $hx))

set_option hygiene false in
/-- Load `b[j]` again (its byte known). -/
macro "ldagain " j:term ", " hx:ident : tactic => `(tactic| (
  rw [if_pos (show 0 ≤ sint.Z $j ∧ sint.Z $j < sint.Z b.len by word)]
  wp_apply wp_load_slice_index b (sint.Z $j) bs dq _ (by word) $$ [Hs] as Hs
  · iframe; ipureintro; rw [show (sint.Z $j).toNat = uint.nat $j by word]; exact $hx))

set_option hygiene false in
/-- Return the pair `e` says `N` is. -/
macro "fin_ret " e:term : tactic => `(tactic| (
  iapply pair_finish Φ _ _ _ _ _ (by rw [$e:term]; try rfl) (by rw [$e:term]; try word) $$ HΦ
  iexact Hs))


end spec

end models_lab.jsoncodec
end Perennial
