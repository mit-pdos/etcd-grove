/-
The proof of `ConditionsAwareDecision.UnconditionalPartsOrFailClosed.spec` (`Spec/k8s_io/apiserver
/pkg/authorization/authorizer/ConditionsAwareDecision__UnconditionalPartsOrFailClosed.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__UnconditionalPartsOrFailClosed
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsNoOpinion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsAllow
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Reason
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Error
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__FailureDecision
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__PossibleDecisions
public import Spec.k8s_io.apimachinery.pkg.util.sets.ListW
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.Decision__String
public import Perennial.Spec.fmt.Sprintf
public import Proof.fmt.SprintfPure
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.SliceRange
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethods
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethodsB1
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.B1Lemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer

/-! The loop spelling out the possible decisions is proved by `wp_slice_for_range_ro`, at the
`slice.forRange` it is about, not unfolded by `wp_auto`. -/
attribute [-instance] pure_wp_slice_for_range

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

theorem ConditionsAwareDecision.UnconditionalPartsOrFailClosed.wp_proof
    (wp_ConditionsAwareDecision_IsDeny : EtcdGrove.authorizer.ConditionsAwareDecision.IsDeny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsNoOpinion : EtcdGrove.authorizer.ConditionsAwareDecision.IsNoOpinion.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsAllow : EtcdGrove.authorizer.ConditionsAwareDecision.IsAllow.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_Reason : EtcdGrove.authorizer.ConditionsAwareDecision.Reason.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_Error : EtcdGrove.authorizer.ConditionsAwareDecision.Error.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_FailureDecision : EtcdGrove.authorizer.ConditionsAwareDecision.FailureDecision.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_PossibleDecisions : EtcdGrove.authorizer.ConditionsAwareDecision.PossibleDecisions.spec (GF := GF) (hG := hG))
    (wp_List : EtcdGrove.sets.List'.specW (GF := GF) (hG := hG))
    (wp_Decision_String : EtcdGrove.authorizer.Decision.String.spec (GF := GF) (hG := hG))
    (wp_Sprintf : _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG)) :
    ConditionsAwareDecision.UnconditionalPartsOrFailClosed.spec (GF := GF) (hG := hG) := by
  intro d m
  wp_start as #Hd
  simp only [DecisionDeny, DecisionNoOpinion, DecisionAllow]
  wp_auto
  wp_apply (ConditionsAwareDecision.wp_ptr_IsDeny_of wp_ConditionsAwareDecision_IsDeny d_ptr
    (DFrac.own 1) d) $$ [$d] as Hdp
  cases h0 : decide (d.decisionType' = W64 0)
  rotate_left
  · wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_Reason_of wp_ConditionsAwareDecision_Reason d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    wp_apply (ConditionsAwareDecision.wp_ptr_Error_of wp_ConditionsAwareDecision_Error d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    iapply HΦ; itrivial
  wp_auto
  wp_apply (ConditionsAwareDecision.wp_ptr_IsNoOpinion_of wp_ConditionsAwareDecision_IsNoOpinion d_ptr
    (DFrac.own 1) d) $$ [$Hdp] as Hdp
  cases h12 : decide (d.decisionType' = W64 12)
  rotate_left
  · wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_Reason_of wp_ConditionsAwareDecision_Reason d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    wp_apply (ConditionsAwareDecision.wp_ptr_Error_of wp_ConditionsAwareDecision_Error d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    iapply HΦ; itrivial
  wp_auto
  wp_apply (ConditionsAwareDecision.wp_ptr_IsAllow_of wp_ConditionsAwareDecision_IsAllow d_ptr
    (DFrac.own 1) d) $$ [$Hdp] as Hdp
  cases h11 : decide (d.decisionType' = W64 11)
  rotate_left
  · wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_Reason_of wp_ConditionsAwareDecision_Reason d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    wp_apply (ConditionsAwareDecision.wp_ptr_Error_of wp_ConditionsAwareDecision_Error d_ptr
      (DFrac.own 1) d) $$ [$Hdp] as Hdp
    iapply HΦ; itrivial
  wp_auto
  wp_apply (ConditionsAwareDecision.wp_ptr_FailureDecision_of wp_ConditionsAwareDecision_FailureDecision
    d_ptr (DFrac.own 1) d m) $$ [$Hdp] as Hdp
  · iexact Hd
  wp_apply (ConditionsAwareDecision.wp_ptr_PossibleDecisions_of wp_ConditionsAwareDecision_PossibleDecisions
    d_ptr (DFrac.own 1) d m) $$ [$Hdp] as %s ⟨⟨%S, HS, %HSm⟩, Hdp⟩
  · iexact Hd
  wp_apply (wp_List s (DFrac.own 1) S (setIs_size_le_b1 HSm)) $$ [$HS] as %sl %ks ⟨HS, Hsl, %Hks⟩
  -- the possible decisions spelled out, as `%v` prints a `[]Decision` (without its brackets)
  wp_apply (wp_slice_for_range_ro (V := w64) _ sl ks (DFrac.own 1) _
    (fun _ => iprop(∃ (ps : GoString), possible_ptr ↦ ps ∗ (∃ x : w64, p_ptr ↦ x) ∗
      ∃ j : w64, i_ptr ↦ j))) $$ [$Hsl] [possible p i]
  · iexists _; iframe
  · imodintro
    iintro %j %x %hx ⟨%ps, possible, ⟨%x0, p⟩, %j0, i⟩ Hsl
    wp_auto
    wp_if_destruct
    · wp_apply (Decision.wp_ptr_String_of wp_Decision_String p_ptr (DFrac.own 1) _) $$ [$p] as %str Hp
      try wp_auto
      isplitr
      · ipureintro; rfl
      iframe
    · wp_apply (Decision.wp_ptr_String_of wp_Decision_String p_ptr (DFrac.own 1) _) $$ [$p] as %str Hp
      try wp_auto
      isplitr
      · ipureintro; rfl
      iframe
  iintro ⟨%ps, possible, ⟨%x0, p⟩, %j0, i⟩ Hsl
  wp_auto
  wp_apply (Decision.wp_ptr_String_of wp_Decision_String failureDecision_ptr (DFrac.own 1) _)
    $$ [$failureDecision] as %str Hfd
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk go.string #ps, interface.mkOk go.string #str]
  isplitr
  · ipureintro; rfl
  iintro %asl ⟨Hasl, -⟩
  try wp_auto
  wp_apply (EtcdGrove.fmt.wp_Sprintf_pure wp_Sprintf
    go!"failed closed from conditional decision (with possible outcomes [%s]) to %s during unconditional authorization"
    [.lit go!"failed closed from conditional decision (with possible outcomes [",
      .dir none _root_.Perennial.fmt.verb_s, .lit go!"]) to ",
      .dir none _root_.Perennial.fmt.verb_s, .lit go!" during unconditional authorization"]
    _ [interface.mkOk go.string #ps, interface.mkOk go.string #str] _ (DFrac.own 1)
    (by fmt_encode) (by fmt_fits) (.str _ _ _ (.str _ _ _ .nil))) $$ [$Hasl] as %r ⟨Hasl, -⟩
  iapply HΦ; itrivial

end proof

end authorizer
end EtcdGrove
end Perennial
