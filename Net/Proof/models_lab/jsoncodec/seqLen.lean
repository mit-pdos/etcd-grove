/-
The proof of `jsoncodec.seqLen` (`Net/Spec/models_lab/jsoncodec/seqLen.lean`).
-/
module

public import Net.Spec.models_lab.jsoncodec.seqLen
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

/-- A leaf of `seqLen`'s proof: `seqLenOf`'s result is `seqLenAt`. -/
theorem seqLen_leaf (Φ : val → IProp GF) (s : List w8) (j : Nat) (a b c d : w8)
    (h : seqLenB a b c d = seqLenAt s j) :
    (True -∗ Φ #(W64 (seqLenAt s j : Int))) ⊢ Φ #(W64 (seqLenB a b c d : Int)) := by
  rw [h]; iintro H; iapply H; itrivial

set_option hygiene false in
local macro "leaf_tac" : tactic => `(tactic| (
  unfold seqLenAt
  try rw [e1]
  try rw [e2]
  try rw [e3]
  repeat' first
    | (rw [hz (uint.nat i + 1) (by word)])
    | (rw [hz (uint.nat i + 2) (by word)])
    | (rw [hz (uint.nat i + 3) (by word)])))

set_option linter.unreachableTactic false in
theorem seqLen.wp_proof (wp_seqLenOf : seqLenOf.spec (GF := GF) (hG := hG)) :
    seqLen.spec (GF := GF) (hG := hG) := by
  intro s i hi
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hlen
  try wp_auto
  have hz : ∀ k, s.length ≤ k → s.getD k (W8 0) = W8 0 := fun k hk => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]; rfl
  have e1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
  have e2 : uint.nat (i + W64 2) = uint.nat i + 2 := by word
  have e3 : uint.nat (i + W64 3) = uint.nat i + 3 := by word
  repeat' (first | (rw [strIdx_some s _ (by word) hlen]) | wp_if_destruct | wp_auto)
  all_goals
    wp_apply wp_seqLenOf
    try wp_auto
    first
    | iapply (seqLen_leaf Φ s (uint.nat i) (s.getD (uint.nat i) (W8 0)) (s.getD (uint.nat (i + W64 1)) (W8 0)) (s.getD (uint.nat (i + W64 2)) (W8 0)) (s.getD (uint.nat (i + W64 3)) (W8 0)) (by leaf_tac)) $$ HΦ
    | iapply (seqLen_leaf Φ s (uint.nat i) (s.getD (uint.nat i) (W8 0)) (s.getD (uint.nat (i + W64 1)) (W8 0)) (s.getD (uint.nat (i + W64 2)) (W8 0)) (W8 0) (by leaf_tac)) $$ HΦ
    | iapply (seqLen_leaf Φ s (uint.nat i) (s.getD (uint.nat i) (W8 0)) (s.getD (uint.nat (i + W64 1)) (W8 0)) (W8 0) (s.getD (uint.nat (i + W64 3)) (W8 0)) (by leaf_tac)) $$ HΦ
    | iapply (seqLen_leaf Φ s (uint.nat i) (s.getD (uint.nat i) (W8 0)) (s.getD (uint.nat (i + W64 1)) (W8 0)) (W8 0) (W8 0) (by leaf_tac)) $$ HΦ
    | iapply (seqLen_leaf Φ s (uint.nat i) (s.getD (uint.nat i) (W8 0)) (W8 0) (s.getD (uint.nat (i + W64 2)) (W8 0)) (s.getD (uint.nat (i + W64 3)) (W8 0)) (by leaf_tac)) $$ HΦ
    | iapply (seqLen_leaf Φ s (uint.nat i) (s.getD (uint.nat i) (W8 0)) (W8 0) (s.getD (uint.nat (i + W64 2)) (W8 0)) (W8 0) (by leaf_tac)) $$ HΦ
    | iapply (seqLen_leaf Φ s (uint.nat i) (s.getD (uint.nat i) (W8 0)) (W8 0) (W8 0) (s.getD (uint.nat (i + W64 3)) (W8 0)) (by leaf_tac)) $$ HΦ
    | iapply (seqLen_leaf Φ s (uint.nat i) (s.getD (uint.nat i) (W8 0)) (W8 0) (W8 0) (W8 0) (by leaf_tac)) $$ HΦ

end proof

end models_lab.jsoncodec
end Perennial
