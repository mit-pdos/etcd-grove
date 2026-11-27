/-
Shared lemmas of the proofs of `jsoncodec`'s decoding helpers: `SkipSpace` at a byte that is
not whitespace (`wp_SkipSpace_ns`, from `SkipSpace`'s spec), `valD_take_succ`, and the internal
`noEscape` (`wp_noEscape`). Ported from dsverify-lab's `GoDec.lean`
(`examples/vr/proof/VsrProof/Proof/jsoncodec/`, lab master 915f964); `wp_noEscape` is new (the
lab's `QuotedUint` had no `noEscape`).
-/
module

public import Net.Spec.models_lab.jsoncodec.SkipSpace
public import Net.Proof.models_lab.jsoncodec.ScanString
public import Net.Proof.models_lab.jsoncodec.Scan.Lits

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

theorem w64_finish (Φ : val → IProp GF) (P : IProp GF) (a b : w64) (h : a = b) :
    (P -∗ Φ #a) ⊢ P -∗ Φ #b := by
  subst h; iintro H; iexact H

theorem skipEnd_ns' (bs : List w8) (i : Nat) (c : w8) (h : bs[i]? = some c)
    (hc : JsonScan.spB c = false) : JsonScan.skipEnd bs i = i := by
  simp only [JsonScan.skipEnd, JsonScan.drop_cons_of bs i c h, List.takeWhile_cons, hc]
  simp

/-- `SkipSpace` at a byte that is not whitespace. -/
theorem wp_SkipSpace_ns (wp_SkipSpace : SkipSpace.spec (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (c : w8)
    (hc : bs[uint.nat i]? = some c) (hs : JsonScan.spB c = false) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (App (Val (@! models_lab.jsoncodec.SkipSpace)) (Val #b)) (Val #i))
    {{ RET #i; b ↦*{dq} bs }} := by
  wp_start_folded as Hs
  have hi : uint.nat i ≤ bs.length := by
    rcases Nat.lt_or_ge (uint.nat i) bs.length with h | h
    · omega
    · rw [List.getElem?_eq_none h] at hc; cases hc
  wp_apply (wp_SkipSpace b dq bs i hi) $$ Hs as Hs
  have := skipEnd_ns' bs _ c hc hs
  rw [this]
  rw [show W64 ((uint.nat i : Nat) : Int) = i by word]
  iapply HΦ; iexact Hs

theorem valD_take_succ (ds : List w8) (m : Nat) (c : w8) (h : ds[m]? = some c) :
    JsonScan.valD (ds.take (m + 1)) = JsonScan.valD (ds.take m) * 10 + (c.toNat - 48) := by
  rw [List.take_succ, h]; simp [JsonScan.valD_append, JsonScan.valD_single]

/-- `noEscape(b, i, j)` on bytes `b[i:j]` none of which is a backslash: returns. -/
theorem wp_noEscape (b : GoSlice) (dq : DFrac) (bs : List w8) (i j : w64)
    (hj : uint.nat j ≤ bs.length)
    (hne : ∀ (k : Nat) (x : w8), uint.nat i ≤ k → k < uint.nat j → bs[k]? = some x → x ≠ W8 92) :
    {{ (b ↦*{dq} bs : IProp GF) }}
      (App (App (App (Val (@! models_lab.jsoncodec.noEscape)) (Val #b)) (Val #i)) (Val #j))
    {{ RET #(); b ↦*{dq} bs }} := by
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := len_lt b bs Hlen
  wp_auto
  ihave IH : iprop(∃ (kw : w64), "k" ∷ k_ptr ↦ kw ∗ "%Hk" ∷ ⌜uint.nat i ≤ uint.nat kw⌝) $$ [k]
  · iexists _; iframe; ipureintro; omega
  wp_for IH
  wp_if_destruct
  · ldidx kw, x, Hx
    have hx := hne _ x Hk (by word) Hx
    wp_if_destruct
    · exfalso; first | exact hx Hif | exact hx rfl | (apply hx; simpa using Hif)
    wp_for_post
    iframe
    iexists _
    iframe
    ipureintro
    word
  · iapply HΦ; iexact Hs

end spec

end models_lab.jsoncodec
end Perennial
