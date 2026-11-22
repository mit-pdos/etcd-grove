/-
The proof of `AuthorizerFunc.ConditionsAwareAuthorize.spec` (`Spec/k8s_io/apiserver/pkg/authorizat
ion/authorizer/AuthorizerFunc__ConditionsAwareAuthorize.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.AuthorizerFunc__ConditionsAwareAuthorize
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.AuthorizerFunc__Authorize
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionFromParts

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

theorem AuthorizerFunc.ConditionsAwareAuthorize.wp_proof
    (wp_AuthorizerFunc_Authorize : EtcdGrove.authorizer.AuthorizerFunc.Authorize.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionFromParts : EtcdGrove.authorizer.ConditionsAwareDecisionFromParts.spec (GF := GF) (hG := hG)) :
    AuthorizerFunc.ConditionsAwareAuthorize.spec (GF := GF) (hG := hG) := by
  have wp_ptr_Authorize : ∀ (l : Loc) (f : GoFunc) (ctx a : GoInterface),
      {{ l ↦ f ∗ authzFnOk (GF := GF) f }}
        (App (App (Val (l @!! go.GoType.PointerType AuthorizerFunc.ty @!! go!"Authorize"))
          (Val #ctx)) (Val #a))
      {{ (dec : w64) (r : GoString) (e : GoInterface), RET (PairV (PairV #dec #r) #e); l ↦ f ∗
          utilerrors.errTreeOrNil e }} := by
    intro l f ctx a
    wp_start as ⟨Hl, #Hf⟩
    wp_auto
    wp_apply (wp_AuthorizerFunc_Authorize f ctx a) as %dec %r %e #He
    · iexact Hf
    iapply HΦ
    iframe
    iexact He
  intro f ctx a
  wp_start as #Hf
  wp_auto
  wp_apply (wp_ptr_Authorize f_ptr f ctx a) $$ [$f] as %dec %r %e ⟨Hfp, #He⟩
  · iexact Hf
  wp_apply (wp_ConditionsAwareDecisionFromParts dec r e) $$ [] as %d #Hd
  · iexact He
  iapply HΦ
  unfold isWFDecisionLe
  iexists _
  iframe Hd
  ipureintro
  exact ⟨Dec.ofWord_WF dec, by simp [Dec.ofWord_depth]⟩

end proof

end authorizer
end EtcdGrove
end Perennial
