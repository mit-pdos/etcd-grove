/-
The proof of `ConditionsAwareDecisionConditionsMap.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/ConditionsAwareDecisionConditionsMap.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionNoOpinion
public import Spec.fmt.ErrorfLeaf
public import Spec.k8s_io.apimachinery.pkg.util.sets.New
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.validateConditions
public import Spec.slices.Clone
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.B2Lemmas

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

theorem ConditionsAwareDecisionConditionsMap.wp_proof
    (wp_ConditionsAwareDecisionDeny : EtcdGrove.authorizer.ConditionsAwareDecisionDeny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionNoOpinion : EtcdGrove.authorizer.ConditionsAwareDecisionNoOpinion.spec (GF := GF) (hG := hG))
    (wp_ErrorfLeaf : EtcdGrove.fmt.ErrorfLeaf.spec (GF := GF) (hG := hG))
    (wp_sets_New : EtcdGrove.sets.New.spec (GF := GF) (hG := hG))
    (wp_validateConditions : EtcdGrove.authorizer.validateConditions.spec (GF := GF) (hG := hG))
    (wp_Clone : EtcdGrove.slices.Clone.spec (GF := GF) (hG := hG)) :
    ConditionsAwareDecisionConditionsMap.spec (GF := GF) (hG := hG) := by
  intro sd sn sa qd qn qa dn no al
  wp_start as ⟨Hsd, Hsn, Hsa, #Hcs⟩
  ihave %Hld := ownSlice_len _ _ _ $$ Hsd
  ihave %Hln := ownSlice_len _ _ _ $$ Hsn
  ihave %Hla := ownSlice_len _ _ _ $$ Hsa
  wp_auto
  by_cases h0 : sd.len + sn.len + sa.len = W64 0
  · simp only [h0, _root_.decide_true]
    wp_auto
    wp_apply wp_ErrorfLeaf _ slice.nil ([] : List GoInterface) (DFrac.own 1) as %ef ⟨-, #Hef, %hef⟩
    · isplitr; · iapply ownSlice_nil
      fmt_args_ok
    ihave #Hte := utilerrors.errTreeOrNil_of_errOk ef hef $$ Hef
    wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
    · iexact Hte
    iapply HΦ
    iframe
    unfold isWFDecisionLe
    iexists .noOpinion
    isplitr
    · iexact Hd
    · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
  simp only [h0, _root_.decide_false]
  wp_auto
  by_cases h128 : sint.Z (W64 128) < sint.Z (sd.len + sn.len + sa.len)
  · simp only [h128, _root_.decide_true]
    wp_auto
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %sla ⟨Hargs, -⟩
    (try wp_auto)
    wp_apply wp_ErrorfLeaf _ _ _ _ $$ [Hargs] as %ef ⟨-, #Hef, %hef⟩
    · iframe Hargs
      fmt_args_ok
    ihave #Hte := utilerrors.errTreeOrNil_of_errOk ef hef $$ Hef
    (try wp_auto)
    by_cases hdl : sint.Z (W64 0) < sint.Z sd.len
    · simp only [hdl, _root_.decide_true]
      wp_auto
      wp_apply (wp_ConditionsAwareDecisionDeny) $$ [] as %d #Hd
      · first | iassumption | iapply utilerrors.errTreeOrNil_nil
      iapply HΦ
      iframe
      unfold isWFDecisionLe
      iexists .deny
      isplitr
      · iexact Hd
      · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
    · simp only [hdl, _root_.decide_false]
      wp_auto
      wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
      · first | iassumption | iapply utilerrors.errTreeOrNil_nil
      iapply HΦ
      iframe
      unfold isWFDecisionLe
      iexists .noOpinion
      isplitr
      · iexact Hd
      · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
  simp only [h128, _root_.decide_false]
  wp_auto
  -- the fold of a map with only NoOpinion conditions; past it, a Deny or an Allow condition
  by_cases hdz : sd.len = W64 0
  · simp only [hdz, _root_.decide_true]
    wp_auto
    by_cases haz : sa.len = W64 0
    · simp only [haz, _root_.decide_true]
      wp_auto
      wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
      · first | iassumption | iapply utilerrors.errTreeOrNil_nil
      iapply HΦ
      iframe
      unfold isWFDecisionLe
      iexists .noOpinion
      isplitr
      · iexact Hd
      · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
    simp only [haz, _root_.decide_false]
    wp_auto
    have hWF : dn ≠ [] ∨ al ≠ [] := by
      right; intro h; subst h; apply haz; simp at Hla; word
    icases conds_app_b2 (dn ++ no) al $$ Hcs with ⟨#Hrest, #Hal⟩
    icases conds_app_b2 dn no $$ Hrest with ⟨#Hdn, #Hno⟩
    wp_apply (wp_sets_New (K := GoString) (T := go.string) slice.nil (DFrac.own 1) []) as %seen ⟨Hseen, -⟩
    · iapply ownSlice_nil
    (try wp_auto)
    wp_apply (wp_validateConditions seen _ sd qd dn) $$ [Hseen Hsd] as %e1 ⟨⟨%S1, Hseen⟩, Hsd, #Hte1⟩
    · iframe; iexact Hdn
    (try wp_auto)
    rcases e1 with ei1 | _
    · wp_auto
      wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
      · first | iassumption | iapply utilerrors.errTreeOrNil_nil
      iapply HΦ
      iframe
      unfold isWFDecisionLe
      iexists .noOpinion
      isplitr
      · iexact Hd
      · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
    wp_auto
    wp_apply (wp_validateConditions seen _ sn qn no) $$ [Hseen Hsn] as %e2 ⟨⟨%S2, Hseen⟩, Hsn, #Hte2⟩
    · iframe; iexact Hno
    (try wp_auto)
    rcases e2 with ei2 | _
    · wp_auto
      wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
      · first | iassumption | iapply utilerrors.errTreeOrNil_nil
      iapply HΦ
      iframe
      unfold isWFDecisionLe
      iexists .noOpinion
      isplitr
      · iexact Hd
      · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
    wp_auto
    wp_apply (wp_validateConditions seen _ sa qa al) $$ [Hseen Hsa] as %e3 ⟨⟨%S3, Hseen⟩, Hsa, #Hte3⟩
    · iframe; iexact Hal
    (try wp_auto)
    rcases e3 with ei3 | _
    · wp_auto
      wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
      · first | iassumption | iapply utilerrors.errTreeOrNil_nil
      iapply HΦ
      iframe
      unfold isWFDecisionLe
      iexists .noOpinion
      isplitr
      · iexact Hd
      · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
    wp_auto
    iapply wp_fupd
    wp_apply (wp_Clone (V := GoInterface) (E := Condition.ty) sd qd dn) $$ [$Hsd] as %sdc ⟨Hsd, Hcd, -⟩
    ihave Hcdu := ownSlice_persist (V := GoInterface) sdc (DFrac.own 1) dn $$ Hcd
    imod Hcdu with #HcdP
    (try wp_auto)
    wp_apply (wp_Clone (V := GoInterface) (E := Condition.ty) sn qn no) $$ [$Hsn] as %snc ⟨Hsn, Hcn, -⟩
    ihave Hcnu := ownSlice_persist (V := GoInterface) snc (DFrac.own 1) no $$ Hcn
    imod Hcnu with #HcnP
    (try wp_auto)
    wp_apply (wp_Clone (V := GoInterface) (E := Condition.ty) sa qa al) $$ [$Hsa] as %sac ⟨Hsa, Hca, -⟩
    ihave Hcau := ownSlice_persist (V := GoInterface) sac (DFrac.own 1) al $$ Hca
    imod Hcau with #HcaP
    imodintro
    iapply HΦ
    iframe
    unfold isWFDecisionLe isDecision
    iexists (.cmap dn no al)
    isplitr
    · imodintro
      simp only [isDecisionRaw, isConditionsMap, condsOk]
      iframe #
    · ipureintro; exact ⟨hWF, by simp [Dec.depth]⟩
  simp only [hdz, _root_.decide_false]
  wp_auto
  have hWF : dn ≠ [] ∨ al ≠ [] := by
    left; intro h; subst h; apply hdz; simp at Hld; word
  icases conds_app_b2 (dn ++ no) al $$ Hcs with ⟨#Hrest, #Hal⟩
  icases conds_app_b2 dn no $$ Hrest with ⟨#Hdn, #Hno⟩
  wp_apply (wp_sets_New (K := GoString) (T := go.string) slice.nil (DFrac.own 1) []) as %seen ⟨Hseen, -⟩
  · iapply ownSlice_nil
  (try wp_auto)
  wp_apply (wp_validateConditions seen _ sd qd dn) $$ [Hseen Hsd] as %e1 ⟨⟨%S1, Hseen⟩, Hsd, #Hte1⟩
  · iframe; iexact Hdn
  (try wp_auto)
  rcases e1 with ei1 | _
  · wp_auto
    by_cases hdl : sint.Z (W64 0) < sint.Z sd.len
    · simp only [hdl, _root_.decide_true]
      wp_auto
      wp_apply (wp_ConditionsAwareDecisionDeny) $$ [] as %d #Hd
      · first | iassumption | iapply utilerrors.errTreeOrNil_nil
      iapply HΦ
      iframe
      unfold isWFDecisionLe
      iexists .deny
      isplitr
      · iexact Hd
      · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
    · simp only [hdl, _root_.decide_false]
      wp_auto
      wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
      · first | iassumption | iapply utilerrors.errTreeOrNil_nil
      iapply HΦ
      iframe
      unfold isWFDecisionLe
      iexists .noOpinion
      isplitr
      · iexact Hd
      · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
  wp_auto
  wp_apply (wp_validateConditions seen _ sn qn no) $$ [Hseen Hsn] as %e2 ⟨⟨%S2, Hseen⟩, Hsn, #Hte2⟩
  · iframe; iexact Hno
  (try wp_auto)
  rcases e2 with ei2 | _
  · wp_auto
    by_cases hdl : sint.Z (W64 0) < sint.Z sd.len
    · simp only [hdl, _root_.decide_true]
      wp_auto
      wp_apply (wp_ConditionsAwareDecisionDeny) $$ [] as %d #Hd
      · first | iassumption | iapply utilerrors.errTreeOrNil_nil
      iapply HΦ
      iframe
      unfold isWFDecisionLe
      iexists .deny
      isplitr
      · iexact Hd
      · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
    · simp only [hdl, _root_.decide_false]
      wp_auto
      wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
      · first | iassumption | iapply utilerrors.errTreeOrNil_nil
      iapply HΦ
      iframe
      unfold isWFDecisionLe
      iexists .noOpinion
      isplitr
      · iexact Hd
      · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
  wp_auto
  wp_apply (wp_validateConditions seen _ sa qa al) $$ [Hseen Hsa] as %e3 ⟨⟨%S3, Hseen⟩, Hsa, #Hte3⟩
  · iframe; iexact Hal
  (try wp_auto)
  rcases e3 with ei3 | _
  · wp_auto
    by_cases hdl : sint.Z (W64 0) < sint.Z sd.len
    · simp only [hdl, _root_.decide_true]
      wp_auto
      wp_apply (wp_ConditionsAwareDecisionDeny) $$ [] as %d #Hd
      · first | iassumption | iapply utilerrors.errTreeOrNil_nil
      iapply HΦ
      iframe
      unfold isWFDecisionLe
      iexists .deny
      isplitr
      · iexact Hd
      · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
    · simp only [hdl, _root_.decide_false]
      wp_auto
      wp_apply (wp_ConditionsAwareDecisionNoOpinion) $$ [] as %d #Hd
      · first | iassumption | iapply utilerrors.errTreeOrNil_nil
      iapply HΦ
      iframe
      unfold isWFDecisionLe
      iexists .noOpinion
      isplitr
      · iexact Hd
      · ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
  wp_auto
  iapply wp_fupd
  wp_apply (wp_Clone (V := GoInterface) (E := Condition.ty) sd qd dn) $$ [$Hsd] as %sdc ⟨Hsd, Hcd, -⟩
  ihave Hcdu := ownSlice_persist (V := GoInterface) sdc (DFrac.own 1) dn $$ Hcd
  imod Hcdu with #HcdP
  (try wp_auto)
  wp_apply (wp_Clone (V := GoInterface) (E := Condition.ty) sn qn no) $$ [$Hsn] as %snc ⟨Hsn, Hcn, -⟩
  ihave Hcnu := ownSlice_persist (V := GoInterface) snc (DFrac.own 1) no $$ Hcn
  imod Hcnu with #HcnP
  (try wp_auto)
  wp_apply (wp_Clone (V := GoInterface) (E := Condition.ty) sa qa al) $$ [$Hsa] as %sac ⟨Hsa, Hca, -⟩
  ihave Hcau := ownSlice_persist (V := GoInterface) sac (DFrac.own 1) al $$ Hca
  imod Hcau with #HcaP
  imodintro
  iapply HΦ
  iframe
  unfold isWFDecisionLe isDecision
  iexists (.cmap dn no al)
  isplitr
  · imodintro
    simp only [isDecisionRaw, isConditionsMap, condsOk]
    iframe #
  · ipureintro; exact ⟨hWF, by simp [Dec.depth]⟩

end proof

end authorizer
end EtcdGrove
end Perennial
