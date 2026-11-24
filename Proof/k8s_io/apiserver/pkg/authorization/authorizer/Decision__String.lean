/-
The proof of `Decision.String.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/Decision__String.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.fmt.OutLemmas
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.Decision__String
public import Perennial.Spec.fmt.Sprintf

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

theorem Decision.String.wp_proof
    (wp_Sprintf : _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG)) :
    Decision.String.spec (GF := GF) (hG := hG) := by
  intro k
  wp_start
  wp_auto
  by_cases h0 : k = W64 0
  · rw [decide_eq_true h0]
    wp_auto
    iapply HΦ; itrivial
  rw [decide_eq_false h0]
  wp_auto
  by_cases h1 : k = W64 1
  · rw [decide_eq_true h1]
    wp_auto
    iapply HΦ; itrivial
  rw [decide_eq_false h1]
  wp_auto
  by_cases h2 : k = W64 2
  · rw [decide_eq_true h2]
    wp_auto
    iapply HΦ; itrivial
  rw [decide_eq_false h2]
  wp_auto
  wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.int #k]
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  try wp_auto
  wp_apply (EtcdGrove.fmt.wp_Sprintf_pure wp_Sprintf go!"Unknown (%d)" [.lit go!"Unknown (", .dir none _root_.Perennial.fmt.verb_d, .lit go!")"]
    _ [interface.mkOk go.int #k] _ (DFrac.own 1) (by fmt_encode) (by fmt_fits)
    (.int _ _ _ _ (.int k) .nil)) $$ [Hasl] as %str -
  · iexact Hasl
  iapply HΦ; itrivial

end proof

end authorizer
end EtcdGrove
end Perennial
