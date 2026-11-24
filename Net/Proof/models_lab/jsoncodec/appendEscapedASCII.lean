/-
The proof of `jsoncodec.appendEscapedASCII` (`Net/Spec/models_lab/jsoncodec/appendEscapedASCII.lean`).
-/
module

public import Net.Spec.models_lab.jsoncodec.appendEscapedASCII
public import Net.Spec.models_lab.jsoncodec.htmlByte


@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace models_lab.jsoncodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : models_lab.jsoncodec.Assumptions]

set_option goose.wp.extras true

set_option linter.unnecessarySeqFocus false in
theorem appendEscapedASCII.wp_proof (wp_htmlByte : htmlByte.spec (GF := GF) (hG := hG)) :
    appendEscapedASCII.spec (GF := GF) (hG := hG) := by
  intro b bs c
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  repeat' (first
    | wp_if_destruct
    | wp_apply wp_htmlByte
    | (simp only [htmlB])
    | (rw [uintZ_w8 (_ >>> W64 4), shr4_toNat, hexIdx _ (by omega)])
    | (rw [uintZ_w8 (_ &&& W8 15), and15_toNat, hexIdx _ (by omega)])
    | wp_auto
    | (wp_apply wp_slice_literal (V := w8)
       isplitr
       · ipureintro; rfl
       iintro %lsl ⟨Hlsl, -⟩
       wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlsl] as %b'' ⟨Hb, Hcap, -⟩))
  all_goals
    iapply HΦ
    iframe Hcap
    iapply (slice_pts_eq b'' _ _ ?_) $$ Hb
    congr 1
    all_goals first
    | rfl
    | (have e1 : sint.nat (W64 (0 + 1)) = 1 := rfl
       have e2 : sint.nat (W64 (0 + 1 + 1)) = 2 := rfl
       have e3 : sint.nat (W64 (0 + 1 + 1 + 1)) = 3 := rfl
       have e4 : sint.nat (W64 (0 + 1 + 1 + 1 + 1)) = 4 := rfl
       have e5 : sint.nat (W64 (0 + 1 + 1 + 1 + 1 + 1)) = 5 := rfl
       rw [e1, e2, e3, e4, e5]
       unfold escASCII htmlB
       simp only [uintZ_w8] at *
       simp_all (decide := true) <;> (intros; omega))
    | (unfold escASCII htmlB
       simp only [uintZ_w8] at *
       simp_all (decide := true) <;> omega)

end proof

end models_lab.jsoncodec
end Perennial
