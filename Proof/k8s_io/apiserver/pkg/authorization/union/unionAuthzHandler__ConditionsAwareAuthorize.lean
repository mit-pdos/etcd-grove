/-
The proof of `unionAuthzHandler.ConditionsAwareAuthorize.spec` (`Spec/k8s_io/apiserver/pkg/authori
zation/union/unionAuthzHandler__ConditionsAwareAuthorize.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.union.unionAuthzHandler__ConditionsAwareAuthorize
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__Add
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ContainsUnconditionalAllowOrDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__ToDecision
public import Proof.k8s_io.apiserver.pkg.authorization.union.B5Lemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace union

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer k8s_io.apiserver.pkg.authorization.union EtcdGrove.authorizer

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.union.Assumptions]

theorem unionAuthzHandler.ConditionsAwareAuthorize.wp_proof
    (wp_ConditionsAwareDecisionUnion_Add : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.Add.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_ContainsUnconditionalAllowOrDeny : EtcdGrove.authorizer.ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_ToDecision : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.ToDecision.spec (GF := GF) (hG := hG)) :
    unionAuthzHandler.ConditionsAwareAuthorize.spec (GF := GF) (hG := hG) := by
  intro h ctx attrs
  wp_start as #Hu
  iunfold isUnionAuthz at Hu
  icases Hu with ⟨%nas, %m, #Hch, #Hchs, #Hm, #Hms⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hch
  wp_auto
  ihave Hb := ownBuilder_zero decisions_ptr $$ decisions
  ihave HI : (∃ (j : w64) (na : NamedAuthorizer) (ks : List Dec), "i" ∷ i_ptr ↦ j ∗
      "curr" ∷ currAuthzHandler_ptr ↦ na ∗ "Hb" ∷ ownBuilder decisions_ptr ks ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z h.chain'.len⌝ ∗
      "a" ∷ a_ptr ↦ attrs ∗ "ctx" ∷ ctx_ptr ↦ ctx : IProp GF) $$ [-HΦ «$res0»]
  · iexists W64 0, _, []
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  by_cases hlt : sint.Z j < sint.Z h.chain'.len
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    wp_auto
    obtain ⟨na', hv⟩ : ∃ v, nas[sint.nat j]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z h.chain'.len := ⟨Hj.1, hlt⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index h.chain' (sint.Z j) nas _ na' Hj.1) $$ [Hch] as -
    · iframe #; ipureintro; simpa [sint.nat] using hv
    ihave #Ha := (BigSepL.bigSepL_lookup (Φ := fun _ na => isAuthorizer (GF := GF) na.Authorizer') hv) $$ Hchs
    iunfold isAuthorizer at Ha
    icases Ha with ⟨%ai, %Hai, #Hcaa, #Hec⟩
    rw [Hai]
    simp only
    ispecialize Hcaa $$ %ctx %attrs
    iunfold caaOk at Hcaa
    wp_bind (App (App (Val _) _) _)
    iapply Hcaa
    · itrivial
    iintro !> %d Hwfd
    iunfold isWFDecisionLe at Hwfd
    icases Hwfd with ⟨%md, #Hd, %Hmd⟩
    wp_auto
    wp_apply (wp_ConditionsAwareDecisionUnion_Add decisions_ptr ks na'.AuthorizerName' d md) $$ [$Hb] as Hb
    · iframe #
      ipureintro; exact ⟨Hmd.1, by have := Hmd.2; omega⟩
    (try wp_auto)
    wp_apply (wp_ptr_ContainsUnconditionalAllowOrDeny_of wp_ConditionsAwareDecision_ContainsUnconditionalAllowOrDeny)
      $$ [$decision] as decision
    · iexact Hd
    cases md.cuad
    · wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, na', _
      iframe
      ipureintro; constructor <;> word
    · wp_auto
      wp_apply (wp_ConditionsAwareDecisionUnion_ToDecision decisions_ptr _) $$ [$Hb] as %d' ⟨#Hd', Hb⟩
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iapply isWFDecisionLe_isWFDecision
      iexact Hd'
  · simp only [hlt, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_apply (wp_ConditionsAwareDecisionUnion_ToDecision decisions_ptr ks) $$ [$Hb] as %d ⟨#Hd, Hb⟩
    (try wp_auto)
    iapply HΦ
    iapply isWFDecisionLe_isWFDecision
    iexact Hd

end proof

end union
end EtcdGrove
end Perennial
