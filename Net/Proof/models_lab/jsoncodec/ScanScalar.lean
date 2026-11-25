/-
`jsoncodec.scanLiteral` and `scanScalar` against the Lean scanner (internal functions: `Scan`'s
proof uses these lemmas). Ported from dsverify-lab's
`examples/vr/proof/VsrProof/Proof/jsoncodec/GoScan.lean` (lab master 915f964).
-/
module

public import Net.Proof.models_lab.jsoncodec.ScanNumber
public import Net.Proof.models_lab.jsoncodec.Scan.Idx
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true

/-- `scanLiteral(b, i, lit)`. -/
theorem wp_scanLiteral (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (lit : GoString)
    (hi : uint.nat i ≤ bs.length) (hl : lit.length ≤ 8) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (App (App (Val (@! models_lab.jsoncodec.scanLiteral)) (Val #b)) (Val #i))
        (Val #lit))
    {{ RET (PairV #(W64 ((JsonScan.litL (bs.drop (uint.nat i)) (uint.nat i) lit).1 : Int))
          #(W64 ((JsonScan.litL (bs.drop (uint.nat i)) (uint.nat i) lit).2 : Int)));
        b ↦*{dq} bs }} := by
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := len_lt b bs Hlen
  generalize hN : JsonScan.litL (bs.drop (uint.nat i)) (uint.nat i) lit = N
  simp only [models_lab.jsoncodec.Done, models_lab.jsoncodec.More,
    models_lab.jsoncodec.Bad]
  wp_auto
  ihave IH : iprop(∃ (jw : w64),
      "j" ∷ j_ptr ↦ jw ∗
      "%Hj" ∷ ⌜uint.nat jw ≤ lit.length ∧ uint.nat i + uint.nat jw ≤ bs.length ∧
        N = JsonScan.litL (bs.drop (uint.nat (i + jw))) (uint.nat (i + jw)) (lit.drop (uint.nat jw))⌝)
      $$ [j]
  · iexists _; iframe; ipureintro
    refine ⟨by simp, by simp; omega, ?_⟩
    rw [← hN]; simp
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len (str := lit) as %-
  wp_if_destruct
  · have hc : uint.Z jw < uint.Z (W64 lit.length) := by
      have := go.intoVal_inj Hif; simpa using this
    have hjl : uint.nat jw < lit.length := by word
    have hij : uint.nat (i + jw) = uint.nat i + uint.nat jw := by word
    wp_if_destruct
    · wp_for_post
      rw [JsonScan.litL_more bs _ lit _ hjl (by word)] at Hj
      fin_ret Hj.2.2
    · ldidx (i + jw), c, Hc
      obtain ⟨l, Hl⟩ : ∃ l, lit[uint.nat jw]? = some l := ⟨_, List.getElem?_eq_getElem hjl⟩
      rw [show (if 0 ≤ sint.Z jw then lit[sint.nat jw]? else none) = some l by
        rw [if_pos (by word), show sint.nat jw = uint.nat jw by word, Hl]]
      simp only
      wp_pures
      wp_if_destruct
      · wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [Hj.2.2, hij, JsonScan.litL_ok bs _ lit _ hjl (by
          rw [← hij, Hc, (List.getElem_eq_iff hjl).2 Hl, Hif])]
        rw [show uint.nat (i + (jw + W64 1)) = uint.nat i + uint.nat jw + 1 by word,
          show uint.nat (jw + W64 1) = uint.nat jw + 1 by word]
      · wp_for_post
        rw [hij, JsonScan.litL_bad bs _ lit _ hjl c (by rw [← hij]; exact Hc) (by
          intro h; apply Hif; rw [h, (List.getElem_eq_iff hjl).2 Hl])] at Hj
        rw [← hij] at Hj
        fin_ret Hj.2.2
  · have hc : ¬ uint.Z jw < uint.Z (W64 lit.length) := by
      intro h; apply Hif; simp only [decide_eq_true h]
    simp only [decide_eq_false hc, Bool.false_eq_true, if_false, ite_false]
    wp_auto
    have hjl : lit.length ≤ uint.nat jw := by word
    rw [JsonScan.litL_done bs _ lit _ hjl] at Hj
    fin_ret Hj.2.2

/-- `scanScalar(b, i, eof)`. -/
theorem wp_scanScalar (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (eof : Bool)
    (hi : uint.nat i < bs.length) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (App (App (Val (@! models_lab.jsoncodec.scanScalar)) (Val #b)) (Val #i))
        (Val #eof))
    {{ RET (PairV #(W64 ((JsonScan.scalarL (bs.drop (uint.nat i)) (uint.nat i) eof).1 : Int))
          #(W64 ((JsonScan.scalarL (bs.drop (uint.nat i)) (uint.nat i) eof).2 : Int)));
        b ↦*{dq} bs }} := by
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := len_lt b bs Hlen
  generalize hN : JsonScan.scalarL (bs.drop (uint.nat i)) (uint.nat i) eof = N
  simp only [models_lab.jsoncodec.Done, models_lab.jsoncodec.More,
    models_lab.jsoncodec.Bad]
  wp_auto
  ldidx i, c, Hc
  have hdc := JsonScan.drop_cons_of bs _ c Hc
  rw [hdc] at hN
  wp_if_destruct
  · simp only [JsonScan.scalarL] at hN
    wp_apply wp_scanString b dq bs i hi $$ Hs as Hs
    simp at hN
    fin_ret hN.symm
  have h34 : c ≠ 34#8 := by intro h; apply Hif; rw [h]; rfl
  have hnum : (c = 45#8 ∨ JsonScan.isDig c = true) →
      N = JsonScan.numL (bs.drop (uint.nat i)) (uint.nat i) eof := by
    intro h; rw [← hN, hdc]; simp only [JsonScan.scalarL, h34, h, if_false, ite_false, if_true, ite_true]
  wp_if_destruct
  · wp_apply wp_scanNumber b dq bs i eof hi $$ Hs as Hs
    fin_ret (hnum (Or.inl rfl))
  have h45 : c ≠ 45#8 := by intro h; apply Hif; rw [h]; rfl
  wp_apply wp_isDigit c
  by_cases hd : JsonScan.isDig c = true
  · simp only [hd]
    wp_auto
    wp_apply wp_scanNumber b dq bs i eof hi $$ Hs as Hs
    fin_ret (hnum (Or.inr hd))
  simp only [Bool.not_eq_true] at hd
  simp only [hd]
  wp_auto
  have hlit : ∀ lit, (c = 116#8 ∧ lit = go!"true") ∨ (c ≠ 116#8 ∧ c = 102#8 ∧ lit = go!"false") ∨
      (c ≠ 116#8 ∧ c ≠ 102#8 ∧ c = 110#8 ∧ lit = go!"null") →
      N = JsonScan.litL (bs.drop (uint.nat i)) (uint.nat i) lit := by
    intro lit h; rw [← hN, hdc]
    rcases h with ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, h3, rfl⟩ <;>
      simp [JsonScan.scalarL, h34, h45, hd, h1] <;> simp_all
  wp_if_destruct
  · wp_apply wp_scanLiteral b dq bs i _ (by omega) (by decide) $$ Hs as Hs
    fin_ret (hlit _ (Or.inl ⟨rfl, rfl⟩))
  have h116 : c ≠ 116#8 := by intro h; apply Hif; rw [h]; rfl
  wp_if_destruct
  · wp_apply wp_scanLiteral b dq bs i _ (by omega) (by decide) $$ Hs as Hs
    fin_ret (hlit _ (Or.inr (Or.inl ⟨by decide, rfl, rfl⟩)))
  have h102 : c ≠ 102#8 := by intro h; apply Hif; rw [h]; rfl
  wp_if_destruct
  · wp_apply wp_scanLiteral b dq bs i _ (by omega) (by decide) $$ Hs as Hs
    fin_ret (hlit _ (Or.inr (Or.inr ⟨by decide, by decide, rfl, rfl⟩)))
  have h110 : c ≠ 110#8 := by intro h; apply Hif; rw [h]; rfl
  have e : N = (2, uint.nat i) := by
    rw [← hN]; simp [JsonScan.scalarL, h34, h45, hd, h116, h102, h110]
  fin_ret e

end spec

end models_lab.jsoncodec
end Perennial
