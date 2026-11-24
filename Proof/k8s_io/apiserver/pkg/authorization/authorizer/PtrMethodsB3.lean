/-
Lean-first (no Rocq counterpart).

More of the `*ConditionsAwareDecision` method set's wrappers of `ConditionsAwareDecision`'s value
methods (as `PtrMethods.lean`), for `collectReasonsAndErrors`, which holds its decision in a local
variable: `IsDeny`, `IsNoOpinion`, `IsUnion`, `Reason`, `Error`, `UnionedDecisions`.
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsNoOpinion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Reason
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Error
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__UnionedDecisions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ContainsUnconditionalAllowOrDeny
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__UnsortedList
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Clone

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

/-- `(*ConditionsAwareDecision).IsDeny` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_IsDeny_of
    (wp_IsDeny : ConditionsAwareDecision.IsDeny.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"IsDeny")) (Val #()))
    {{ RET #(decide (d.decisionType' = W64 0)); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_IsDeny d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).IsNoOpinion` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_IsNoOpinion_of
    (wp_IsNoOpinion : ConditionsAwareDecision.IsNoOpinion.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"IsNoOpinion"))
        (Val #()))
    {{ RET #(decide (d.decisionType' = W64 12)); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_IsNoOpinion d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).IsUnion` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_IsUnion_of
    (wp_IsUnion : ConditionsAwareDecision.IsUnion.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"IsUnion")) (Val #()))
    {{ RET #(decide (d.decisionType' = W64 14)); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_IsUnion d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).Reason` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_Reason_of
    (wp_Reason : ConditionsAwareDecision.Reason.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"Reason")) (Val #()))
    {{ RET #(d.reason'); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_Reason d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).Error` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_Error_of
    (wp_Error : ConditionsAwareDecision.Error.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) :
    {{ (l ↦{dl} d : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"Error")) (Val #()))
    {{ RET #(d.err'); l ↦{dl} d }} := by
  wp_start as Hl
  wp_auto
  wp_apply (wp_Error d)
  iapply HΦ; iframe

/-- `(*ConditionsAwareDecision).UnionedDecisions` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_UnionedDecisions_of
    (wp_UnionedDecisions : ConditionsAwareDecision.UnionedDecisions.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) (nds : List namedConditionsAwareDecision) :
    {{ (l ↦{dl} d ∗ d.union'.inner' ↦*□ nds : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!! go!"UnionedDecisions"))
        (Val #()))
    {{ (f : GoFunc), RET #f; l ↦{dl} d ∗
        seq2Ok (GF := GF) f (nds.map (fun nd => (nd.conditionalAuthorizerName', nd.d'))) }} := by
  wp_start as ⟨Hl, #Hs⟩
  wp_auto
  wp_apply (wp_UnionedDecisions d nds) as %f #Hf
  · iexact Hs
  iapply HΦ; iframe; iexact Hf

/-- `(*ConditionsAwareDecision).ContainsUnconditionalAllowOrDeny` on the decision `*l`. -/
theorem ConditionsAwareDecision.wp_ptr_ContainsUnconditionalAllowOrDeny_of
    (wp_CUAD : ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (d : ConditionsAwareDecision) (m : Dec) :
    {{ (l ↦{dl} d ∗ isDecision d m : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType ConditionsAwareDecision.ty @!!
        go!"ContainsUnconditionalAllowOrDeny")) (Val #()))
    {{ RET #(m.cuad); l ↦{dl} d }} := by
  wp_start as ⟨Hl, #Hd⟩
  wp_auto
  wp_apply (wp_CUAD d m)
  · iexact Hd
  iapply HΦ; iframe

end wps

section setwps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]
variable {K : Type} [ZeroVal K] [DecidableEq K] [go.IntoValInj K] [TypedPointsto (GF := GF) K]
  {T : go.GoType} [IntoValTyped (GF := GF) K T]

open k8s_io.apimachinery.pkg.util.sets in
/-- `(*Set[T]).UnsortedList` on the set `*l`. -/
theorem sets_wp_ptr_UnsortedList_of (wp_UnsortedList : sets.Set.UnsortedList.spec (GF := GF) (hG := hG))
    (l : Loc) (dl : DFrac) (m : Loc) (dq : DFrac) (s : GMap K sets.Elem) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗
        l ↦{dl} (m : Set'' K) ∗ m ↦${dq} s }}
      (App (Val (l @!! go.GoType.PointerType (Set''.ty T) @!! go!"UnsortedList")) (Val #()))
    {{ (sl : GoSlice) (ks : List K), RET #sl; l ↦{dl} (m : Set'' K) ∗ m ↦${dq} s ∗ sl ↦* ks ∗
        ⌜(∀ k, k ∈ ks ↔ (s !! k).isSome) ∧ ks.Nodup ∧ ks.length = GMap.size s⌝ }} := by
  wp_start as ⟨Hl, Hm⟩
  wp_auto
  wp_apply wp_UnsortedList (T := T) $$ [$Hm] as %sl %ks ⟨Hm, Hsl, %Hks⟩
  iapply HΦ; iframe; ipureintro; exact Hks

open k8s_io.apimachinery.pkg.util.sets in
/-- `(*Set[T]).Clone` on the set `*l`. -/
theorem sets_wp_ptr_Clone_of (wp_Clone : sets.Set.Clone.spec (GF := GF) (hG := hG))
    [∀ k : K, SafeMapKey (GF := GF) T k]
    (l : Loc) (dl : DFrac) (m : Loc) (dq : DFrac) (s : GMap K sets.Elem) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.util.sets ∗
        l ↦{dl} (m : Set'' K) ∗ m ↦${dq} s }}
      (App (Val (l @!! go.GoType.PointerType (Set''.ty T) @!! go!"Clone")) (Val #()))
    {{ (r : Loc), RET #r; l ↦{dl} (m : Set'' K) ∗ m ↦${dq} s ∗ r ↦$ s }} := by
  wp_start as ⟨Hl, Hm⟩
  wp_auto
  wp_apply wp_Clone (T := T) $$ [$Hm] as %r ⟨Hm, Hr⟩
  iapply HΦ; iframe

end setwps

end authorizer
end EtcdGrove
end Perennial
