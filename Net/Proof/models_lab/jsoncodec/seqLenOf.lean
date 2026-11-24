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

theorem seqLenOf.wp_proof : seqLenOf.spec (GF := GF) (hG := hG) := by
  intro c c1 c2 c3
  wp_start
  wp_auto
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals
    rw [show (_ : w64) = W64 (seqLenB c c1 c2 c3 : Int) by
      congr 1; unfold seqLenB loB hiB; simp_all]
    iapply HΦ
    itrivial

end proof

end models_lab.jsoncodec
end Perennial
