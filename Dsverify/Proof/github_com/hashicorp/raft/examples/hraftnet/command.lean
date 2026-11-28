/-
`hraftnet.command`'s proof: the kind byte, `opID`'s bytes appended, a put's value appended.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.command
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.opID

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

set_option goose.wp.extras true

theorem command.wp_proof (wp_opID : opID.spec (GF := GF)) : command.spec (GF := GF) := by
  intro c s put way v
  wp_start as -
  wp_auto
  cases put
  · simp only
    wp_auto
    wp_apply wp_slice_literal (V := w8) [W8 71]
    isplitr
    · ipureintro; rfl
    iintro %lp ⟨Hl, Hlc⟩
    try wp_auto
    wp_apply wp_opID as %o ⟨Ho, -⟩
    wp_apply wp_slice_append (V := w8) $$ [$Hl $Hlc $Ho] as %b2 ⟨Hb2, -, -⟩
    try wp_auto
    iapply HΦ
    unfold cmdB
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show W8 71 :: opIDB c s = [W8 71] ++ opIDB c s from rfl]
    iexact Hb2
  · simp only
    wp_auto
    wp_apply wp_slice_literal (V := w8) [W8 80]
    isplitr
    · ipureintro; rfl
    iintro %lp ⟨Hl, Hlc⟩
    try wp_auto
    wp_apply wp_opID as %o ⟨Ho, -⟩
    wp_apply wp_slice_append (V := w8) $$ [$Hl $Hlc $Ho] as %b2 ⟨Hb2, Hcap2, -⟩
    try wp_auto
    wp_apply wp_string_to_bytes as %ss ⟨Hss, -⟩
    wp_apply wp_slice_append (V := w8) $$ [$Hb2 $Hcap2 $Hss] as %b3 ⟨Hb3, -, -⟩
    try wp_auto
    iapply HΦ
    unfold cmdB
    simp only [↓reduceIte]
    rw [show W8 80 :: opIDB c s ++ v = [W8 80] ++ opIDB c s ++ v from rfl]
    iexact Hb3

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
