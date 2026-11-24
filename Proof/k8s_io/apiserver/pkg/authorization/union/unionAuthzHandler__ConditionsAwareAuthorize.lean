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
  icases Hu with ⟨%nas, %m, #Hch, #Hchs, #Hm, #Hms, %Hnas⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hch
  wp_auto
  ihave Hb := ownBuilder_zero decisions_ptr authzNameMax $$ decisions
  ihave HI : (∃ (j : w64) (na : NamedAuthorizer) (ks : List Dec), "i" ∷ i_ptr ↦ j ∗
      "curr" ∷ currAuthzHandler_ptr ↦ na ∗ "Hb" ∷ ownBuilder decisions_ptr ks authzNameMax ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z h.chain'.len⌝ ∗
      "%Hks" ∷ ⌜(Dec.sizeL ks : Int) ≤ sint.Z j * authzSizeMax ∧ Dec.depthL ks ≤ authzDepthMax⌝ ∗
      "a" ∷ a_ptr ↦ attrs ∗ "ctx" ∷ ctx_ptr ↦ ctx : IProp GF) $$ [-HΦ «$res0»]
  · iexists W64 0, _, []
    iframe
    ipureintro; refine ⟨by constructor <;> word, by simp [Dec.sizeL], by simp [Dec.depthL]⟩
  have hnl : nas.length ≤ authzChainMax := Hnas.1
  have hfit : ∀ ks : List Dec, (Dec.sizeL ks : Int) ≤ nas.length * authzSizeMax →
      Dec.depthL ks ≤ authzDepthMax → Dec.foldFits authzNameMax (.union ks) := by
    intro ks h1 h2
    refine Dec.foldFits_of_le _ _ (authzChainMax * authzSizeMax + 1) (authzDepthMax + 1) ?_ ?_
      authz_foldBound_lt
    · simp only [Dec.size]
      have := Nat.mul_le_mul_right authzSizeMax hnl
      omega
    · simp only [Dec.depth]; omega
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
    iunfold isWFDecisionBnd at Hwfd
    icases Hwfd with ⟨%md, #Hd, %Hmd, #Hdn⟩
    have hks' : (Dec.sizeL (if Dec.cuadL ks then ks else ks ++ [md]) : Int) ≤
        sint.Z (j + W64 1) * authzSizeMax ∧
        Dec.depthL (if Dec.cuadL ks then ks else ks ++ [md]) ≤ authzDepthMax := by
      have h1 := Dec.sizeL_add_le (Dec.cuadL ks) ks md (Dec.sizeL ks + md.size) (Nat.le_refl _)
      have h2 := Dec.depthL_add_le (Dec.cuadL ks) ks md authzDepthMax Hks.2 Hmd.2.1
      have h3 : sint.Z (j + W64 1) = sint.Z j + 1 := by word
      have h4 := Hmd.2.2
      refine ⟨?_, h2⟩
      rw [h3, Int.add_mul, Int.one_mul]
      have := Hks.1
      omega
    have hjn : sint.Z j + 1 ≤ nas.length := by word
    wp_auto
    wp_apply (wp_ConditionsAwareDecisionUnion_Add decisions_ptr ks na'.AuthorizerName' d md authzNameMax)
      $$ [$Hb] as Hb
    · iframe #
      ipureintro
      refine ⟨Hmd.1, ?_, Hnas.2 _ (List.mem_of_getElem? hv)⟩
      have := Hmd.2.1; unfold authzDepthMax at this; omega
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
      ipureintro; exact ⟨by constructor <;> word, hks'⟩
    · wp_auto
      wp_apply (wp_ConditionsAwareDecisionUnion_ToDecision decisions_ptr _ authzNameMax
        (hfit _ (by have := hks'.1; rw [show sint.Z (j + W64 1) = sint.Z j + 1 by word] at this
                    have h5 : (sint.Z j + 1) * (authzSizeMax : Int) ≤ nas.length * authzSizeMax :=
                      Int.mul_le_mul_of_nonneg_right hjn (by simp)
                    omega) hks'.2)) $$ [$Hb] as %d' ⟨#Hd', Hb⟩
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iapply isWFDecisionBnd_weaken
      isplitl []
      · iexact Hd'
      ipureintro
      constructor
      · have := hks'.2; omega
      · have := hks'.1
        have h5 : (sint.Z (j + W64 1)) * (authzSizeMax : Int) ≤ nas.length * authzSizeMax := by
          rw [show sint.Z (j + W64 1) = sint.Z j + 1 by word]
          exact Int.mul_le_mul_of_nonneg_right hjn (by simp)
        have := Nat.mul_le_mul_right authzSizeMax hnl
        omega
  · simp only [hlt, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    have hjl : sint.Z j ≤ nas.length := by word
    have h5 : sint.Z j * (authzSizeMax : Int) ≤ nas.length * authzSizeMax :=
      Int.mul_le_mul_of_nonneg_right hjl (by simp)
    wp_apply (wp_ConditionsAwareDecisionUnion_ToDecision decisions_ptr ks authzNameMax
      (hfit ks (by have := Hks.1; omega) Hks.2)) $$ [$Hb] as %d ⟨#Hd, Hb⟩
    (try wp_auto)
    iapply HΦ
    iapply isWFDecisionBnd_weaken
    isplitl []
    · iexact Hd
    ipureintro
    constructor
    · have := Hks.2; omega
    · have := Hks.1
      have := Nat.mul_le_mul_right authzSizeMax hnl
      omega

end proof

end union
end EtcdGrove
end Perennial
