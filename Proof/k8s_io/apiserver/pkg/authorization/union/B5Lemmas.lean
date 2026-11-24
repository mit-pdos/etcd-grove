/-
Lean-first (no Rocq counterpart).

Helpers of the union package's proofs (`unionAuthzHandler.EvaluateConditions`, ...): the
`*ConditionsAwareDecision` method set's wrappers of the value methods these proofs call on a local
variable (as `authorizer/PtrMethods.lean`), and the `*unionAuthzHandler` wrapper of
`evaluateConditions`.
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsNoOpinion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Reason
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Error
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__UnionedDecisions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ContainsUnconditionalAllowOrDeny
public import Spec.k8s_io.apiserver.pkg.authorization.union.unionAuthzHandler__evaluateConditions

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace union

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer
  k8s_io.apiserver.pkg.authorization.union EtcdGrove.authorizer

/-- A `WFL` list's elements are `WF`. -/
theorem Dec.WFL_get [GooseExts] : ∀ (ks : List authorizer.Dec) (i : Nat) (k : authorizer.Dec),
    authorizer.Dec.WFL ks → ks[i]? = some k → k.WF
  | [], _, _, _, h => by simp at h
  | k' :: ks, 0, k, hw, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; exact hw.1
  | _ :: ks, i + 1, k, hw, h => by
    simp only [List.getElem?_cons_succ] at h
    exact Dec.WFL_get ks i k hw.2 h

theorem PD.has_zero [GooseExts] (p : authorizer.PD) : p.has (W64 0) = p.deny := by
  unfold authorizer.PD.has; cases p.deny <;> cases p.allow <;> cases p.noOpinion <;> decide
theorem PD.has_one [GooseExts] (p : authorizer.PD) : p.has (W64 1) = p.allow := by
  unfold authorizer.PD.has; cases p.deny <;> cases p.allow <;> cases p.noOpinion <;> decide
theorem PD.has_two [GooseExts] (p : authorizer.PD) : p.has (W64 2) = p.noOpinion := by
  unfold authorizer.PD.has; cases p.deny <;> cases p.allow <;> cases p.noOpinion <;> decide

/-- `EvaluateConditions`' loop invariant, one child further: no child before `i + 1` contains an
unconditional Allow or Deny. -/
theorem cuad_step [GooseExts] (ks : List authorizer.Dec) (i : Nat) (mk : authorizer.Dec)
    (H : ∀ j k, j < i → ks[j]? = some k → k.cuad = false) (Hmk : ks[i]? = some mk)
    (h : mk.cuad = false) : ∀ j k, j < i + 1 → ks[j]? = some k → k.cuad = false := by
  intro j k hj hk
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · exact H j k hj hk
  · rw [Hmk] at hk; cases hk; exact h

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.union.Assumptions]

/-- Naming a WP's postcondition (to refer to the code after a loop). -/
theorem wp_post_named (e : Expr) (Φ : val → IProp GF) :
    (∀ K : val → IProp GF, ⌜K = Φ⌝ -∗ WP e {{ K }}) ⊢ WP e {{ Φ }} := by
  iintro H
  iapply H $$ %Φ
  ipureintro; rfl

theorem isDecisionRawL_length : ∀ (ds : List ConditionsAwareDecision) (ks : List authorizer.Dec),
    isDecisionRawL (GF := GF) ds ks ⊢ ⌜ds.length = ks.length⌝
  | [], [] => by iintro -; ipureintro; rfl
  | [], _ :: _ => by simp only [isDecisionRawL]; iintro H; iexfalso; iexact H
  | _ :: _, [] => by simp only [isDecisionRawL]; iintro H; iexfalso; iexact H
  | d :: ds, k :: ks => by
    simp only [isDecisionRawL]
    iintro ⟨-, H⟩
    icases isDecisionRawL_length ds ks $$ H with %Hl
    ipureintro; simp [Hl]

/-- A union's children are as many as their models. -/
theorem isDecisionL_length (ds : List ConditionsAwareDecision) (ks : List authorizer.Dec) :
    isDecisionL (GF := GF) ds ks ⊢ ⌜ds.length = ks.length⌝ := by
  unfold isDecisionL
  iintro #H
  iapply isDecisionRawL_length
  iexact H

theorem wp_ptr_IsUnion_of
    (wp_X : ConditionsAwareDecision.IsUnion.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"IsUnion")) (Val #()))
    {{ RET #(decide (d.decisionType' = W64 14)); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_X d)
  iapply HΦ; iframe

theorem wp_ptr_IsDeny_of
    (wp_X : ConditionsAwareDecision.IsDeny.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"IsDeny")) (Val #()))
    {{ RET #(decide (d.decisionType' = W64 0)); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_X d)
  iapply HΦ; iframe

theorem wp_ptr_IsNoOpinion_of
    (wp_X : ConditionsAwareDecision.IsNoOpinion.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"IsNoOpinion")) (Val #()))
    {{ RET #(decide (d.decisionType' = W64 12)); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_X d)
  iapply HΦ; iframe

theorem wp_ptr_IsConditionsMap_of
    (wp_X : ConditionsAwareDecision.IsConditionsMap.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"IsConditionsMap"))
        (Val #()))
    {{ RET #(decide (d.decisionType' = W64 13)); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_X d)
  iapply HΦ; iframe

theorem wp_ptr_Reason_of
    (wp_X : ConditionsAwareDecision.Reason.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"Reason")) (Val #()))
    {{ RET #(d.reason'); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_X d)
  iapply HΦ; iframe

theorem wp_ptr_Error_of
    (wp_X : ConditionsAwareDecision.Error.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"Error")) (Val #()))
    {{ RET #(d.err'); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_X d)
  iapply HΦ; iframe

theorem wp_ptr_ContainsUnconditionalAllowOrDeny_of
    (wp_X : ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) (m : authorizer.Dec) :
    {{ (l ↦{dl} d ∗ isDecision d m : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!!
        go!"ContainsUnconditionalAllowOrDeny")) (Val #()))
    {{ RET #(m.cuad); l ↦{dl} d }} := by
  iintro %Φ ⟨Hl, #Hd⟩ HΦ
  wp_method_call; (try wp_call)
  wp_auto
  iapply (wp_X d m)
  · iexact Hd
  iintro !> -
  iapply HΦ
  iframe

theorem wp_ptr_UnionedDecisions_of
    (wp_X : ConditionsAwareDecision.UnionedDecisions.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) (nds : List namedConditionsAwareDecision) :
    {{ (l ↦{dl} d ∗ d.union'.inner' ↦*□ nds : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"UnionedDecisions"))
        (Val #()))
    {{ (f : GoFunc), RET #f;
        seq2Ok (GF := GF) f (nds.map (fun nd => (nd.conditionalAuthorizerName', nd.d'))) ∗
        l ↦{dl} d }} := by
  iintro %Φ ⟨Hl, #Hs⟩ HΦ
  wp_method_call; (try wp_call)
  wp_auto
  iapply (wp_X d nds)
  · iexact Hs
  iintro !> %f Hf
  iapply HΦ
  iframe

theorem wp_ptr_evaluateConditions_of
    (wp_X : unionAuthzHandler.evaluateConditions.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (h : unionAuthzHandler) (ctx : GoInterface) (name : GoString)
    (d : ConditionsAwareDecision) (data : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.union ∗
        l ↦{dl} h ∗ isUnionAuthz h ∗ isWFDecisionFit authzNameMax d }}
      (App (App (App (App (Val (l @!! go.GoType.PointerType unionAuthzHandler.ty @!! go!"evaluateConditions"))
        (Val #ctx)) (Val #name)) (Val #d)) (Val #data))
    {{ (dec : w64) (r : GoString) (e : GoInterface), RET (PairV (PairV #dec #r) #e); l ↦{dl} h }} := by
  iintro %Φ ⟨#Hpkg, Hl, #Hu, #Hd⟩ HΦ
  wp_method_call; (try wp_call)
  wp_auto
  iapply (wp_X h ctx name d data)
  · iframe #
  iintro !> %dec %r %e -
  iapply HΦ
  iframe

end wps

end union
end EtcdGrove
end Perennial
