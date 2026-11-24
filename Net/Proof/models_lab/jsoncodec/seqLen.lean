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

theorem seqLen.wp_proof (wp_seqLenOf : seqLenOf.spec (GF := GF) (hG := hG)) :
    seqLen.spec (GF := GF) (hG := hG) := by
  intro s i hi
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hlen
  wp_auto
  have hz : ∀ k, s.length ≤ k → s.getD k (W8 0) = W8 0 := fun k hk => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]; rfl
  repeat' (first | (rw [strIdx_some s _ (by word) hlen]) | wp_if_destruct | wp_auto)
  all_goals trace_state
  all_goals sorry

end proof

end models_lab.jsoncodec
end Perennial
