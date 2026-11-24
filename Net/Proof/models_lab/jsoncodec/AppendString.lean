/-
The proof of `jsoncodec.AppendString` (`Net/Spec/models_lab/jsoncodec/AppendString.lean`) on a
plain string: the check loop (`plainByte`, `htmlByte` true/false on each byte), then the quotes
and the bytes appended. Ported from dsverify-lab's `wp_AppendString` (`GoEnc.lean`, lab master
915f964).
-/
module

public import Net.Spec.models_lab.jsoncodec.AppendString
public import Net.Proof.models_lab.jsoncodec.ScanString
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true
set_option maxHeartbeats 2000000

theorem wp_plainByte_ok (c : w8)
    (h : 32 ≤ c.toNat ∧ c.toNat ≤ 126 ∧ c.toNat ≠ 34 ∧ c.toNat ≠ 92) :
    {{ (True : IProp GF) }}
      (App (Val (@! models_lab.jsoncodec.plainByte)) (Val #c))
    {{ RET #true; True }} := by
  have h1 : uint.Z (W8 32) ≤ uint.Z c := by simp [uint.Z]; omega
  have h2 : uint.Z c ≤ uint.Z (W8 126) := by simp [uint.Z]; omega
  have h3 : c ≠ W8 34 := by intro e; subst e; simp at h
  have h4 : c ≠ W8 92 := by intro e; subst e; simp at h
  wp_start
  wp_auto
  repeat (simp only [decide_eq_true h1, decide_eq_true h2, decide_eq_false h3,
    decide_eq_false h4, BitVec.le_def] ; wp_auto)
  simp only [decide_eq_false h4, Bool.not_false]
  iapply HΦ; itrivial

theorem wp_htmlByte_ok (c : w8) (h : c.toNat ≠ 60 ∧ c.toNat ≠ 62 ∧ c.toNat ≠ 38) :
    {{ (True : IProp GF) }}
      (App (Val (@! models_lab.jsoncodec.htmlByte)) (Val #c))
    {{ RET #false; True }} := by
  have h1 : c ≠ W8 60 := by intro e; subst e; simp at h
  have h2 : c ≠ W8 62 := by intro e; subst e; simp at h
  have h3 : c ≠ W8 38 := by intro e; subst e; simp at h
  wp_start
  wp_auto
  repeat (simp only [decide_eq_false h1, decide_eq_false h2, decide_eq_false h3] ; wp_auto)
  simp only [decide_eq_false h3]
  iapply HΦ; itrivial

theorem AppendString.wp_proof : AppendString.spec (GF := GF) (hG := hG) := by
  intro b bs str hs
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  ihave IH : iprop(∃ i : w64, "i" ∷ i_ptr ↦ i ∗ "%Hi" ∷ ⌜uint.nat i ≤ str.length⌝) $$ [i]
  · iexists _; iframe; ipureintro; simp
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hlen
  by_cases Hif : sint.Z i < sint.Z (W64 ↑str.length)
  · rw [decide_eq_true Hif, if_pos (by simp)]
    wp_auto
    have Hlt : sint.nat i < str.length := by word
    obtain ⟨c, Hc⟩ : ∃ c, str[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have hpc := hs c (List.mem_of_getElem? Hc)
    rw [if_pos (show 0 ≤ sint.Z i by word), Hc]
    wp_auto
    wp_apply wp_plainByte_ok c ⟨hpc.1, hpc.2.1, hpc.2.2.1, hpc.2.2.2.1⟩
    try rw [if_pos (show 0 ≤ sint.Z i by word), Hc]
    try wp_auto
    wp_apply wp_htmlByte_ok c ⟨hpc.2.2.2.2.1, hpc.2.2.2.2.2.1, hpc.2.2.2.2.2.2⟩
    try wp_auto
    wp_for_post
    iframe
    iexists _
    iframe
    ipureintro
    word
  · rw [decide_eq_false Hif, if_neg (by simp only [decide_eq_true_eq]; intro h; have := go.intoVal_inj h; simp at this),
      if_pos (by simp)]
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [W8 34]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b1 ⟨Hb1, Hcap1, -⟩
    wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb1 $Hcap1 $Hsl] as %b2 ⟨Hb2, Hcap2, -⟩
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [W8 34]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb2 $Hcap2 $Hlit] as %b3 ⟨Hb3, Hcap3, -⟩
    iapply HΦ
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    iframe
end proof

end models_lab.jsoncodec
end Perennial
