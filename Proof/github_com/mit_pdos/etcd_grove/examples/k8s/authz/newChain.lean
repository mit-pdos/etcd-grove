/-
The proof of `newChain.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/newChain.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.newChain
public import Spec.k8s_io.apiserver.pkg.authorization.union.New
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbAuthorizer__ConditionsAwareAuthorize
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbAuthorizer__EvaluateConditions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.AuthorizerFunc__ConditionsAwareAuthorize
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.AuthorizerFunc__EvaluateConditions
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.legacyAuthorize

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

theorem newChain.wp_proof
    (wp_New : EtcdGrove.union.New.spec (GF := GF) (hG := hG))
    (wp_arbAuthorizer_ConditionsAwareAuthorize : EtcdGrove.k8s_authz.arbAuthorizer.ConditionsAwareAuthorize.spec (GF := GF) (hG := hG))
    (wp_arbAuthorizer_EvaluateConditions : EtcdGrove.k8s_authz.arbAuthorizer.EvaluateConditions.spec (GF := GF) (hG := hG))
    (wp_AuthorizerFunc_ConditionsAwareAuthorize : EtcdGrove.authorizer.AuthorizerFunc.ConditionsAwareAuthorize.spec (GF := GF) (hG := hG))
    (wp_AuthorizerFunc_EvaluateConditions : EtcdGrove.authorizer.AuthorizerFunc.EvaluateConditions.spec (GF := GF) (hG := hG))
    (wp_legacyAuthorize : EtcdGrove.k8s_authz.legacyAuthorize.spec (GF := GF) (hG := hG)) :
    newChain.spec (GF := GF) (hG := hG) := by
  wp_start
  ihave #Harb : (∀ z : arbAuthorizer,
      ⌜uint.nat z.depth' ≤ authzDepthMax ∧ 4 ^ uint.nat z.depth' ≤ authzSizeMax⌝ -∗
      isAuthorizer (interface.mkOk arbAuthorizer.ty #z) : IProp GF) $$ []
  · iintro %z %hz
    iunfold isAuthorizer
    iexists ⟨arbAuthorizer.ty, #z⟩
    isplitr
    · ipureintro; rfl
    isplitr
    · iintro %ctx %attrs
      iunfold caaOk
      iintro !> %Ψ _ HΨ
      wp_apply (wp_arbAuthorizer_ConditionsAwareAuthorize z ctx attrs hz.1 hz.2) as %d #Hd
      iapply HΨ
      iexact Hd
    · iintro %ctx %d %data
      iunfold ecOk
      iintro !> %Ψ #Hwf HΨ
      wp_apply (wp_arbAuthorizer_EvaluateConditions z ctx d data) as %dec %r %e _
      · iexact Hwf
      iapply HΨ
      itrivial
  ihave #Hleg : (isAuthorizer (interface.mkOk AuthorizerFunc.ty #(functions legacyAuthorize []))
      : IProp GF) $$ []
  · iunfold isAuthorizer
    iexists ⟨AuthorizerFunc.ty, #(functions legacyAuthorize [])⟩
    isplitr
    · ipureintro; rfl
    isplitr
    · iintro %ctx %attrs
      iunfold caaOk
      iintro !> %Ψ _ HΨ
      wp_apply (wp_AuthorizerFunc_ConditionsAwareAuthorize (functions legacyAuthorize []) ctx attrs)
        as %d #Hd'
      · iunfold authzFnOk
        iintro %c %a
        iunfold authzCallOk
        iintro !> %Ψ' _ HΨ'
        wp_apply (wp_legacyAuthorize c a) as %dec %r %e #He
        iapply HΨ'
        iexact He
      iapply HΨ
      iapply isWFDecisionBnd_weaken
      isplitl []
      · iapply isWFDecisionLe_zero_bnd
        iexact Hd'
      ipureintro; unfold authzDepthMax authzSizeMax; omega
    · iintro %ctx %d %data
      iunfold ecOk
      iintro !> %Ψ _ HΨ
      wp_apply (wp_AuthorizerFunc_EvaluateConditions (functions legacyAuthorize []) ctx d data)
        as %e _
      iapply HΨ
      itrivial
  wp_auto
  wp_apply (wp_slice_literal (l := [
      ({ AuthorizerName' := go!"a",
         Authorizer' := interface.mkOk arbAuthorizer.ty #({ depth' := W64 2 } : arbAuthorizer) }
        : NamedAuthorizer),
      { AuthorizerName' := go!"legacy",
        Authorizer' := interface.mkOk AuthorizerFunc.ty #(functions legacyAuthorize []) },
      { AuthorizerName' := go!"b",
        Authorizer' := interface.mkOk arbAuthorizer.ty #({ depth' := W64 2 } : arbAuthorizer) }]))
  isplitr
  · ipureintro; rfl
  iintro %sp ⟨Hs, -⟩
  ipersist Hs
  (try wp_auto)
  wp_apply (wp_New _ _) as %a %err Hres
  · iframe #
    have h2 : uint.nat (W64 2) = 2 := by word
    isplitl []
    · isplitr
      · iapply Harb
        ipureintro
        exact ⟨by unfold authzDepthMax; word, by rw [h2]; unfold authzSizeMax; decide⟩
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iapply Harb
        ipureintro
        exact ⟨by unfold authzDepthMax; word, by rw [h2]; unfold authzSizeMax; decide⟩
      iapply BigSepL.bigSepL_nil.2
      itrivial
    ipureintro
    refine ⟨by unfold authzChainMax; simp, fun na hna => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hna
    unfold authzNameMax
    rcases hna with rfl | rfl | rfl <;> simp
  (try wp_auto)
  iapply HΦ
  iexact Hres

end proof

end k8s_authz
end EtcdGrove
end Perennial
