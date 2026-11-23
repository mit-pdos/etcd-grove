/-
The proof of `modelPathByte` (`Net/Spec/net/http/modelPathByte.lean`): its comparisons are `pathByte`'s.
-/
module

public import Net.Spec.net.http.modelPathByte

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions]

set_option maxHeartbeats 2000000 in
theorem modelPathByte.wp_proof : modelPathByte.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start
  cases hp : pathByte c
  all_goals
    wp_auto
    iterate 30 (all_goals try (first | wp_if_destruct | wp_auto))
  all_goals first
    | (iapply HΦ; itrivial)
    | (exfalso; revert hp; simp only [pathByte, decide_eq_true_eq, decide_eq_false_iff_not,
        List.mem_cons, List.not_mem_nil, _root_.or_false, _root_.not_or, _root_.not_and]; intro hp; word)

end proof

end net.http
end Perennial
