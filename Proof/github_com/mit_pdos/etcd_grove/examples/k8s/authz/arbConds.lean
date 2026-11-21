/-
The proof of `arbConds.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/arbConds.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbConds
public import Spec.math.rand.Int63n
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbID
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbType
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbCondition__GetID
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbCondition__GetType
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbCondition__GetCondition
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbCondition__GetDescription
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbCondition__Evaluate

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

theorem arbConds.wp_proof
    (wp_Int63n : EtcdGrove.rand.Int63n.spec (GF := GF) (hG := hG))
    (wp_arbID : EtcdGrove.k8s_authz.arbID.spec (GF := GF) (hG := hG))
    (wp_arbType : EtcdGrove.k8s_authz.arbType.spec (GF := GF) (hG := hG))
    (wp_arbCondition_GetID : EtcdGrove.k8s_authz.arbCondition.GetID.spec (GF := GF) (hG := hG))
    (wp_arbCondition_GetType : EtcdGrove.k8s_authz.arbCondition.GetType.spec (GF := GF) (hG := hG))
    (wp_arbCondition_GetCondition : EtcdGrove.k8s_authz.arbCondition.GetCondition.spec (GF := GF) (hG := hG))
    (wp_arbCondition_GetDescription : EtcdGrove.k8s_authz.arbCondition.GetDescription.spec (GF := GF) (hG := hG))
    (wp_arbCondition_Evaluate : EtcdGrove.k8s_authz.arbCondition.Evaluate.spec (GF := GF) (hG := hG)) :
    arbConds.spec (GF := GF) (hG := hG) := by
  wp_start
  ihave #Hcond : (∀ c : arbCondition, isCondition (interface.mkOk arbCondition.ty #c) : IProp GF) $$ []
  · iintro %c
    iunfold isCondition
    iexists ⟨arbCondition.ty, #c⟩
    isplitr
    · ipureintro; rfl
    isplitr
    · iunfold strMethodOk
      iintro !> %Ψ _ HΨ
      wp_apply (wp_arbCondition_GetID c)
      iapply HΨ; itrivial
    isplitr
    · iunfold strMethodOk
      iintro !> %Ψ _ HΨ
      wp_apply (wp_arbCondition_GetType c)
      iapply HΨ; itrivial
    isplitr
    · iunfold strMethodOk
      iintro !> %Ψ _ HΨ
      wp_apply (wp_arbCondition_GetCondition c)
      iapply HΨ; itrivial
    isplitr
    · iunfold strMethodOk
      iintro !> %Ψ _ HΨ
      wp_apply (wp_arbCondition_GetDescription c)
      iapply HΨ; itrivial
    iintro %ctx %data
    iunfold condEvalOk
    iintro !> %Ψ _ HΨ
    wp_apply (wp_arbCondition_Evaluate c ctx data) as %r #Hr
    iapply HΨ; iexact Hr
  wp_auto
  wp_apply wp_Int63n as %n %Hn
  · ipureintro; decide
  (try wp_auto)
  ihave HI : (∃ (j : w64) (s : GoSlice) (cl : List GoInterface),
      "i" ∷ i_ptr ↦ j ∗ "cs" ∷ cs_ptr ↦ s ∗ "Hs" ∷ s ↦* cl ∗
      "Hcap" ∷ ownSliceCap GoInterface s (DFrac.own 1) ∗
      "Hcl" ∷ [∗list] c ∈ cl, isCondition c : IProp GF) $$ [i cs]
  · iexists W64 0, slice.nil, []
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    iunfold named
    iapply BigSepL.bigSepL_nil.2
    itrivial
  wp_for HI
  by_cases Hlt : sint.Z j < sint.Z n
  · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
    (try wp_auto)
    wp_apply wp_arbID as %id _
    (try wp_auto)
    wp_apply wp_arbType as %ty _
    (try wp_auto)
    wp_apply (wp_slice_literal (l := [interface.mkOk arbCondition.ty #(arbCondition.mk id ty)]))
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hosl] as %s' ⟨Hs', Hcap', -⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists _, s', _
    iframe
    iapply BigSepL.bigSepL_singleton.2
    iapply Hcond
  · rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    iapply HΦ
    iexists cl
    iframe

end proof

end k8s_authz
end EtcdGrove
end Perennial
