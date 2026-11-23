/-
The proof of `strconv.Atoi`'s value spec (`AtoiSpec.lean`) over Perennial's translation of
`strconv.Atoi` and `internal/strconv.Atoi` (`internal/strconv/atoi.go`'s fast path: 1 to 18 bytes,
no sign, every byte a digit), adapted from the lab's `Harness/Proof/strconv/Atoi.lean` (over its
own translation); and the instance `atoiSpec_inst` the `Results` modules use.
-/
module

public import Dsverify.Proof.raxos.AtoiSpec
public import Perennial.Golang.Theory.String

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos.hyp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open strconv (decVal smallDigits)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [Perennial.strconv.Assumptions]

set_option goose.wp.extras true

/-- `internal/strconv.Atoi(s)` on its fast path, for 1 to 18 decimal digits: the value. -/
theorem wp_internal_Atoi_digits (s : GoString) (hs : smallDigits s) :
    {{ (True : IProp GF) }}
      (App (Val (@! Perennial.internal.strconv.Atoi)) (Val #s))
    {{ RET (PairV #(W64 (decVal s)) #GoInterface.nil); True }} := by
  obtain ⟨hl1, hl2, hd⟩ := hs
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hlen
  wp_pures
  wp_if_destruct
  rotate_left
  · exfalso; apply Hif; word
  wp_if_destruct
  rotate_left
  · exfalso; apply Hif; word
  obtain ⟨c, cs, rfl⟩ : ∃ c cs, s = c :: cs := by
    cases s with
    | nil => simp at hl1
    | cons c cs => exact ⟨c, cs, rfl⟩
  have hcd := hd c (List.mem_cons_self ..)
  have h45 : c ≠ W8 45 := by intro h; subst h; simp at hcd
  have h43 : c ≠ W8 43 := by intro h; subst h; simp at hcd
  simp only [List.getElem?_cons_zero]
  wp_auto
  rw [decide_eq_false h45]
  wp_auto
  rw [decide_eq_false h43]
  wp_auto
  generalize hsd : c :: cs = s at *
  wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
  ihave %Hsll := ownSlice_len $$ Hsl
  ihave IH : iprop(∃ (j : w64) (cv : w8), "i" ∷ i_ptr ↦ j ∗ "ch" ∷ ch_ptr ↦ cv ∗
      "n" ∷ n_ptr ↦ W64 (decVal (s.take (sint.Z j).toNat)) ∗ "Hsl" ∷ sl ↦* s ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (s.length : Int)⌝) $$ [i ch n Hsl]
  · iexists _, _
    iframe
    isplitl
    · simp [decVal]; iexact n
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z j).toNat < s.length := by word
    obtain ⟨b, Hb⟩ : ∃ b, s[(sint.Z j).toNat]? = some b := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbd := hd b (List.mem_of_getElem? Hb)
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len by word]
    wp_apply wp_load_slice_index sl (sint.Z j) s (DFrac.own 1) b Hj.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hb
    have hnot : ¬ uint.Z (W8 9) < uint.Z (b - W8 48) := by
      have h1 := Hbd.1; have h2 := Hbd.2
      simp only [uint.Z] at *
      bv_omega
    rw [decide_eq_false hnot]
    wp_auto
    wp_for_post
    iframe
    iexists _, _
    have hj1 : (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 := by word
    have key : decVal (s.take ((sint.Z j).toNat + 1)) =
        decVal (s.take (sint.Z j).toNat) * 10 + (b.toNat - 48) := by
      rw [List.take_add_one, Hb]
      simp [decVal, List.foldl_append]
    have hc : uint.Z (b - W8 48) = ((b.toNat - 48 : Nat) : Int) := by
      have h1 := Hbd.1
      have h2 : (b - W8 48).toNat = b.toNat - 48 := by bv_omega
      simp only [uint.Z, h2]
    rw [hj1, key, hc]
    have hw : W64 ((decVal (s.take (sint.Z j).toNat) : Int)) * W64 10 +
        W64 ((b.toNat - 48 : Nat) : Int) =
        W64 (((decVal (s.take (sint.Z j).toNat) * 10 + (b.toNat - 48) : Nat)) : Int) := by
      word
    rw [hw]
    iframe
    ipureintro
    constructor <;> word
  · have hjl : (sint.Z j).toNat = s.length := by word
    rw [hjl, List.take_length]
    subst hsd
    simp only [List.getElem?_cons_zero]
    wp_auto
    rw [decide_eq_false h45]
    wp_auto
    iapply HΦ
    itrivial

/-- `strconv.Atoi(s)` for a string of 1 to 18 decimal digits: its value, and a `nil` error. -/
theorem strconv.Atoi.wp_proof : strconv.Atoi.spec (GF := GF) (hG := hG) := by
  intro s hs
  wp_start
  wp_auto
  wp_apply wp_internal_Atoi_digits s hs
  iapply HΦ
  itrivial

instance atoiSpec_inst : AtoiSpec GF := ⟨strconv.Atoi.wp_proof⟩

end proof

end Perennial.raxos.hyp
