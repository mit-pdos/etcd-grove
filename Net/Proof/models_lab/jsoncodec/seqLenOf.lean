/-
The proof of `jsoncodec.seqLenOf` (`Net/Spec/models_lab/jsoncodec/seqLenOf.lean`).
-/
module

public import Net.Spec.models_lab.jsoncodec.seqLenOf


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

/-- A leaf of `seqLenOf`'s proof: its result `k` is `seqLenB`'s. -/
theorem seqLenOf_leaf (Φ : val → IProp GF) (k : Nat) (c c1 c2 c3 : w8) (h : seqLenB c c1 c2 c3 = k) :
    (True -∗ Φ #(W64 (seqLenB c c1 c2 c3 : Int))) ⊢ Φ #(W64 (k : Int)) := by
  rw [h]; iintro H; iapply H; itrivial

set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
theorem seqLenOf.wp_proof : seqLenOf.spec (GF := GF) (hG := hG) := by
  intro a0 a1 a2 a3
  wp_start
  wp_auto
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals
    first
    | iapply (seqLenOf_leaf Φ 1 a0 a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 1 (W8 224) a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 1 (W8 237) a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 1 (W8 240) a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 1 (W8 244) a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 2 a0 a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 2 (W8 224) a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 2 (W8 237) a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 2 (W8 240) a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 2 (W8 244) a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 3 a0 a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 3 (W8 224) a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 3 (W8 237) a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 3 (W8 240) a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 3 (W8 244) a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 4 a0 a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 4 (W8 224) a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 4 (W8 237) a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 4 (W8 240) a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ
    | iapply (seqLenOf_leaf Φ 4 (W8 244) a1 a2 a3 (by unfold seqLenB loB hiB; simp_all (decide := true) <;> (repeat' split) <;> omega)) $$ HΦ

end proof

end models_lab.jsoncodec
end Perennial
