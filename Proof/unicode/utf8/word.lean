/-
Proof of `Spec/unicode/utf8/word.lean`. Lean-first.
-/
module

public import Spec.unicode.utf8.word

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.unicode.utf8.Assumptions]

theorem utf8.word.wp_proof : utf8.word.spec (GF := GF) (hG := hG) := fun s hs => by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, r, rfl⟩ :
      ∃ b0 b1 b2 b3 b4 b5 b6 b7 r, s = b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r := by
    match s, hs with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r, _ => exact ⟨_, _, _, _, _, _, _, _, _, rfl⟩
  have hw : utf8.wordOf (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r) =
      (W64 (uint.Z b0) ||| W64 (uint.Z b1) <<< W64 8 ||| W64 (uint.Z b2) <<< W64 16 |||
        W64 (uint.Z b3) <<< W64 24 ||| W64 (uint.Z b4) <<< W64 32 ||| W64 (uint.Z b5) <<< W64 40 |||
        W64 (uint.Z b6) <<< W64 48 ||| W64 (uint.Z b7) <<< W64 56) := rfl
  rw [hw]
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
