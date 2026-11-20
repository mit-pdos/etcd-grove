/-
The proof of `arbResult.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/arbResult.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbResult
public import Spec.math.rand.Int63n
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResultBoolean
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbErr
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionEvaluationResultError
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsEvaluationResultUnevaluatable

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_authz

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer k8s_io.apiserver.pkg.authorization.union github_com.mit_pdos.etcd_grove.examples.k8s.authz EtcdGrove.authorizer EtcdGrove.union

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.authz.Assumptions]

theorem arbResult.wp_proof
    (wp_Int63n : EtcdGrove.rand.Int63n.spec (GF := GF) (hG := hG))
    (wp_ConditionEvaluationResultBoolean : EtcdGrove.authorizer.ConditionEvaluationResultBoolean.spec (GF := GF) (hG := hG))
    (wp_arbErr : EtcdGrove.k8s_authz.arbErr.spec (GF := GF) (hG := hG))
    (wp_ConditionEvaluationResultError : EtcdGrove.authorizer.ConditionEvaluationResultError.spec (GF := GF) (hG := hG))
    (wp_ConditionsEvaluationResultUnevaluatable : EtcdGrove.authorizer.ConditionsEvaluationResultUnevaluatable.spec (GF := GF) (hG := hG)) :
    arbResult.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_Int63n as %x %Hx
  · ipureintro; decide
  have H4 : x = W64 0 ∨ x = W64 1 ∨ x = W64 2 ∨ x = W64 3 := by
    have : sint.Z x = 0 ∨ sint.Z x = 1 ∨ sint.Z x = 2 ∨ sint.Z x = 3 := by
      have h2 : sint.Z (W64 4) = 4 := by rfl
      have := Hx.2; rw [h2] at this; omega
    rcases this with h | h | h | h
    · left; word
    · right; left; word
    · right; right; left; word
    · right; right; right; word
  rcases H4 with rfl | rfl | rfl | rfl
  · wp_auto
    wp_apply wp_ConditionEvaluationResultBoolean
    (try wp_auto)
    iapply HΦ
    itrivial
  · wp_auto
    wp_apply wp_ConditionEvaluationResultBoolean
    (try wp_auto)
    iapply HΦ
    itrivial
  · wp_auto
    wp_apply wp_arbErr as %e _
    (try wp_auto)
    wp_apply wp_ConditionEvaluationResultError as %e' _
    (try wp_auto)
    iapply HΦ
    itrivial
  · wp_auto
    wp_apply wp_ConditionsEvaluationResultUnevaluatable
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end k8s_authz
end EtcdGrove
end Perennial
