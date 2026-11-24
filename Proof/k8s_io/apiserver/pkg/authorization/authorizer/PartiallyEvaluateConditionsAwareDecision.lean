/-
The proof of `PartiallyEvaluateConditionsAwareDecision.spec` (`Spec/k8s_io/apiserver/pkg/authoriza
tion/authorizer/PartiallyEvaluateConditionsAwareDecision.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.PartiallyEvaluateConditionsAwareDecision
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.partiallyEvaluateConditionsMapInternal
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__UnionedDecisions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__Add
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ContainsUnconditionalAllowOrDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__ToDecision
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnconditional
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethodsB4
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.ForRangeB4

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

/-- The spec at the decisions of model `m` (for the induction on `m`). -/
private def pecadAt (m : Dec) : Prop :=
  ∀ (ctx : GoInterface) (d : ConditionsAwareDecision) (data : GoInterface) (f : GoFunc) (N : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.authorization.authorizer ∗ isDecision d m ∗ ⌜m.WF⌝ ∗
      decNames N d m ∗ ⌜Dec.foldFits N m⌝ ∗ maybeEvalFnOk f }}
    (App (App (App (App (Val (@! PartiallyEvaluateConditionsAwareDecision)) (Val #ctx)) (Val #d))
      (Val #data)) (Val #f))
  {{ (d' : ConditionsAwareDecision), RET #d'; isWFDecisionBnd m.depth m.size N d' }}

private theorem WFL_get : ∀ (ks : List Dec) (i : Nat) (m : Dec), Dec.WFL ks → ks[i]? = some m → m.WF
  | [], _, _, _, h => by simp at h
  | k :: ks, 0, m, h, hm => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
    subst hm; exact h.1
  | k :: ks, i + 1, m, h, hm => by
    simp only [List.getElem?_cons_succ] at hm
    exact WFL_get ks i m h.2 hm

private theorem sizeOf_get (ks : List Dec) (i : Nat) (m : Dec) (h : ks[i]? = some m) :
    sizeOf m < sizeOf (Dec.union ks) := by
  have h1 := List.sizeOf_lt_of_mem (List.mem_of_getElem? h)
  simp only [Dec.union.sizeOf_spec]
  omega

/-- Naming a WP's postcondition (to refer to the code after a loop). -/
private theorem wp_post_named (e : Expr) (Φ : val → IProp GF) :
    (∀ K : val → IProp GF, ⌜K = Φ⌝ -∗ WP e {{ K }}) ⊢ WP e {{ Φ }} := by
  iintro H
  iapply H $$ %Φ
  ipureintro; rfl

theorem PartiallyEvaluateConditionsAwareDecision.wp_proof
    (wp_ConditionsAwareDecision_IsConditionsMap : EtcdGrove.authorizer.ConditionsAwareDecision.IsConditionsMap.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_ConditionsMap : EtcdGrove.authorizer.ConditionsAwareDecision.ConditionsMap.spec (GF := GF) (hG := hG))
    (wp_partiallyEvaluateConditionsMapInternal : EtcdGrove.authorizer.partiallyEvaluateConditionsMapInternal.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsUnion : EtcdGrove.authorizer.ConditionsAwareDecision.IsUnion.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_UnionedDecisions : EtcdGrove.authorizer.ConditionsAwareDecision.UnionedDecisions.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_Add : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.Add.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_ContainsUnconditionalAllowOrDeny : EtcdGrove.authorizer.ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_ToDecision : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.ToDecision.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsUnconditional : EtcdGrove.authorizer.ConditionsAwareDecision.IsUnconditional.spec (GF := GF) (hG := hG)) :
    PartiallyEvaluateConditionsAwareDecision.spec (GF := GF) (hG := hG) := by
  suffices H : ∀ (n : Nat) (m : Dec), sizeOf m < n → pecadAt (GF := GF) (hG := hG) m by
    intro ctx d m data f N
    exact H (sizeOf m + 1) m (Nat.lt_succ_self _) ctx d data f N
  intro n
  induction n with
  | zero => intro m h; omega
  | succ n IH =>
  intro m hm ctx d data f N
  wp_start as ⟨#Hd, %Hwf, #Hdn, %Hfit, #Hf⟩
  icases isDecision_tag d m $$ Hd with %Htag
  wp_auto
  wp_apply (ConditionsAwareDecision.wp_ptr_IsConditionsMap_of wp_ConditionsAwareDecision_IsConditionsMap
    unevaluatedDecision_ptr (DFrac.own 1) d) $$ [$unevaluatedDecision] as unevaluatedDecision
  rw [Htag, Dec.tag_cmap]
  cases m
  case cmap dn no al =>
    simp only [Dec.isCMap]
    wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_ConditionsMap_of wp_ConditionsAwareDecision_ConditionsMap
      unevaluatedDecision_ptr (DFrac.own 1) d) $$ [$unevaluatedDecision] as unevaluatedDecision
    (try wp_auto)
    ihave #Hc := isDecision_cmap d dn no al $$ Hd
    wp_apply (wp_partiallyEvaluateConditionsMapInternal ctx d.conditionsMap' dn no al data f) as %d' #Hd'
    · iframe #
    (try wp_auto)
    iapply HΦ
    iapply isWFDecisionBnd_weaken
    isplitl []
    · iapply isWFDecisionLe_zero_bnd
      iexact Hd'
    ipureintro; simp [Dec.depth, Dec.size]
  case union ks =>
    simp only [Dec.isCMap]
    wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsUnion_of wp_ConditionsAwareDecision_IsUnion
      unevaluatedDecision_ptr (DFrac.own 1) d) $$ [$unevaluatedDecision] as unevaluatedDecision
    rw [Htag, Dec.tag_union]
    simp only [Dec.isUnion]
    wp_auto
    icases isDecision_union_names N d ks $$ Hd Hdn with ⟨%nds, #Hnds, #HL, %Hnm, #HN⟩
    wp_apply (ConditionsAwareDecision.wp_ptr_UnionedDecisions_of wp_ConditionsAwareDecision_UnionedDecisions
      unevaluatedDecision_ptr (DFrac.own 1) d nds) $$ [$unevaluatedDecision] as %rng ⟨unevaluatedDecision, #Hrng⟩
    · iexact Hnds
    ihave Hb := ownBuilder_zero newDecisionChain_ptr N $$ newDecisionChain
    have hfitB : ∀ ks' : List Dec, Dec.depthL ks' ≤ Dec.depthL ks → Dec.sizeL ks' ≤ Dec.sizeL ks →
        Dec.foldFits N (.union ks') := fun ks' h1 h2 =>
      Dec.foldFits_of_le N (.union ks') (Dec.union ks).size (Dec.union ks).depth
        (by simp only [Dec.size]; omega) (by simp only [Dec.depth]; omega) Hfit
    wp_bind (App (App (Val (func.forRange 2)) _) _)
    iapply wp_post_named
    iintro %K %hK
    iapply wp_forRange2B4 _ _ _ (by simp) rfl
    iintro %y %Tok %Done HTok #Hy
    iunfold seq2Ok at Hrng
    ihave Hrun := Hrng $$ %y
      %(fun (i : Nat) => iprop(Tok ∗ ∃ (ks' : List Dec) (c : Bool) (u : ConditionsAwareDecision)
        (an : GoString), ownBuilder newDecisionChain_ptr ks' N ∗
        ⌜Dec.depthL ks' ≤ Dec.depthL ks ∧ Dec.sizeL ks' ≤ Dec.sizeL (ks.take i)⌝ ∗
        collectTailAfterConditionalDecision_ptr ↦ c ∗ unevaluatedSubDecision_ptr ↦ u ∗
        authorizerName_ptr ↦ an ∗ «$res0_ptr» ↦ zero_val ConditionsAwareDecision ∗
        evaluateConditionFn_ptr ↦ f ∗ data_ptr ↦ data ∗ ctx_ptr ↦ ctx ∗
        (∀ d', isWFDecisionBnd (Dec.union ks).depth (Dec.union ks).size N d' -∗ Φ #d')))
      %(iprop(∃ r, Done (returnVal r) ∗ K (returnVal r))) []
    · iintro !> %i %k %v %hkv
      have hv : (nds.map (·.d'))[i]? = some v := by
        rw [List.getElem?_map] at hkv ⊢
        cases h : nds[i]? with
        | none => rw [h] at hkv; cases hkv
        | some nd => rw [h] at hkv; cases hkv; rfl
      icases isDecisionL_lookup _ ks i v hv $$ HL with ⟨%m', %hm', #Hv⟩
      ihave #Hvn := decNamesL_lookup N _ ks i v m' hv hm' $$ HN
      have hkN : k.length ≤ N := by
        rw [List.getElem?_map] at hkv
        cases h : nds[i]? with
        | none => rw [h] at hkv; cases hkv
        | some nd =>
          rw [h] at hkv; cases hkv; exact Hnm nd (List.mem_of_getElem? h)
      have hfit' := Dec.foldFits_child N ks i m' hm' Hfit
      have hsz : Dec.sizeL (ks.take (i + 1)) = Dec.sizeL (ks.take i) + m'.size :=
        Dec.sizeL_take_succ ks i m' hm'
      have hwf' : m'.WF := WFL_get ks i m' (by simp only [Dec.WF] at Hwf; exact Hwf.1) hm'
      have hdep' : m'.depth ≤ Dec.depthL ks := Dec.depth_le_depthL ks i m' hm'
      have hdks : Dec.depthL ks + 1 < 2 ^ 63 := by simp only [Dec.WF] at Hwf; exact Hwf.2.2
      have hlt : sizeOf m' < n := by have := sizeOf_get ks i m' hm'; omega
      iunfold yield2Ok
      iintro !> %Ψ ⟨HTok, %ks', %c, %u, %an, Hb, %Hks', Hc, Hu, Han, Hres, Hev, Hdata, Hctx, HΦ⟩ HΨ
      iapply Hy $$ %#k %#v %Ψ [] HTok
      · ipureintro; exact ⟨by simp, by simp⟩
      wp_auto
      cases c
      · -- evaluating the child (recursively)
        wp_auto
        wp_apply (IH m' hlt ctx v data f N) as %d' #Hd'
        · iframe #
          ipureintro; exact ⟨hwf', hfit'⟩
        iunfold isWFDecisionBnd at Hd'
        icases Hd' with ⟨%m'', #Hd'', %hwf'', #Hdn''⟩
        have hks'' : Dec.depthL (if Dec.cuadL ks' then ks' else ks' ++ [m'']) ≤ Dec.depthL ks ∧
            Dec.sizeL (if Dec.cuadL ks' then ks' else ks' ++ [m'']) ≤ Dec.sizeL (ks.take (i + 1)) :=
          ⟨Dec.depthL_add_le (Dec.cuadL ks') ks' m'' (Dec.depthL ks) Hks'.1 (by omega),
           Dec.sizeL_add_le (Dec.cuadL ks') ks' m'' _ (by have := Hks'.2; have := hwf''.2.2; omega)⟩
        wp_apply (wp_ConditionsAwareDecisionUnion_Add newDecisionChain_ptr ks' k d' m'' N) $$ [$Hb] as Hb
        · iframe #
          ipureintro; exact ⟨hwf''.1, by have := hwf''.2.1; omega, hkN⟩
        (try wp_auto)
        wp_apply (ConditionsAwareDecision.wp_ptr_ContainsUnconditionalAllowOrDeny_of
          wp_ConditionsAwareDecision_ContainsUnconditionalAllowOrDeny possiblyEvaluatedSubDecision_ptr
          (DFrac.own 1) d' m'') $$ [$possiblyEvaluatedSubDecision] as possiblyEvaluatedSubDecision
        · iexact Hd''
        cases hcu : m''.cuad
        · wp_auto
          wp_apply (ConditionsAwareDecision.wp_ptr_IsUnconditional_of
            wp_ConditionsAwareDecision_IsUnconditional possiblyEvaluatedSubDecision_ptr (DFrac.own 1) d')
            $$ [$possiblyEvaluatedSubDecision] as possiblyEvaluatedSubDecision
          by_cases hu : (d'.decisionType' = W64 11 ∨ d'.decisionType' = W64 0 ∨
              d'.decisionType' = W64 12)
          · rw [decide_eq_true hu]
            (try wp_auto)
            unfold forRangePostB4
            ileft
            isplitr
            · ipureintro; exact Or.inl rfl
            iintro HTok
            iapply HΨ $$ %true
            simp only [↓reduceIte]
            iframe HTok
            iexists _, _, v, k
            iframe
            ipureintro; exact hks''
          · rw [decide_eq_false hu]
            (try wp_auto)
            unfold forRangePostB4
            ileft
            isplitr
            · ipureintro; exact Or.inl rfl
            iintro HTok
            iapply HΨ $$ %true
            simp only [↓reduceIte]
            iframe HTok
            iexists _, _, v, k
            iframe
            ipureintro; exact hks''
        · -- an unconditional Allow or Deny: the chain's decision is returned
          wp_auto
          wp_apply (wp_ConditionsAwareDecisionUnion_ToDecision newDecisionChain_ptr _ N
            (hfitB _ hks''.1 (Nat.le_trans hks''.2 (Dec.sizeL_take_le ks _)))) $$ [$Hb]
            as %d2 ⟨#Hd2, Hb⟩
          (try wp_auto)
          unfold forRangePostB4
          iright
          isplitr
          · ipureintro; exact Or.inr ⟨_, rfl, by simp⟩
          iintro HD
          iapply HΨ $$ %false
          simp only [Bool.false_eq_true, ↓reduceIte]
          iexists #()
          iframe HD
          rw [hK]
          dsimp only
          wp_auto
          iapply HΦ
          iapply isWFDecisionBnd_weaken
          isplitl []
          · iexact Hd2
          ipureintro
          have := Dec.sizeL_take_le ks (i + 1)
          simp only [Dec.depth, Dec.size]; omega
      · -- collecting the tail: the child as it is
        wp_auto
        have hks'' : Dec.depthL (if Dec.cuadL ks' then ks' else ks' ++ [m']) ≤ Dec.depthL ks ∧
            Dec.sizeL (if Dec.cuadL ks' then ks' else ks' ++ [m']) ≤ Dec.sizeL (ks.take (i + 1)) :=
          ⟨Dec.depthL_add_le (Dec.cuadL ks') ks' m' (Dec.depthL ks) Hks'.1 hdep',
           Dec.sizeL_add_le (Dec.cuadL ks') ks' m' _ (by have := Hks'.2; omega)⟩
        wp_apply (wp_ConditionsAwareDecisionUnion_Add newDecisionChain_ptr ks' k v m' N) $$ [$Hb] as Hb
        · iframe #
          ipureintro; exact ⟨hwf', by omega, hkN⟩
        (try wp_auto)
        unfold forRangePostB4
        ileft
        isplitr
        · ipureintro; exact Or.inr rfl
        iintro HTok
        iapply HΨ $$ %true
        simp only [↓reduceIte]
        iframe HTok
        iexists _, true, v, k
        iframe
        ipureintro; exact hks''
    iunfold iterRunOk at Hrun
    iapply Hrun $$ [HTok Hb collectTailAfterConditionalDecision unevaluatedSubDecision authorizerName
      «$res0» evaluateConditionFn data ctx HΦ]
    · simp only
      iframe HTok
      iexists [], false, _, _
      iframe
      ipureintro; simp [Dec.depthL, Dec.sizeL]
    iintro !> HI
    isplitr
    · ipureintro; simp
    icases HI with (⟨HTok, %ks', %c, %u, %an, Hb, %Hks', Hc, Hu, Han, Hres, Hev, Hdata, Hctx, HΦ⟩ | ⟨%r, HD, HK⟩)
    · ileft
      iframe HTok
      rw [hK]
      dsimp only
      wp_auto
      have hks2 : Dec.sizeL ks' ≤ Dec.sizeL ks :=
        Nat.le_trans Hks'.2 (Dec.sizeL_take_le ks _)
      wp_apply (wp_ConditionsAwareDecisionUnion_ToDecision newDecisionChain_ptr ks' N
        (hfitB _ Hks'.1 hks2)) $$ [$Hb]
        as %d' ⟨#Hd', Hb⟩
      (try wp_auto)
      iapply HΦ
      iapply isWFDecisionBnd_weaken
      isplitl []
      · iexact Hd'
      ipureintro; have := Hks'.1; simp only [Dec.depth, Dec.size]; omega
    · iright; iright
      iexists r
      iframe
  all_goals
    simp only [Dec.isCMap]
    wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_IsUnion_of wp_ConditionsAwareDecision_IsUnion
      unevaluatedDecision_ptr (DFrac.own 1) d) $$ [$unevaluatedDecision] as unevaluatedDecision
    rw [Htag, Dec.tag_union]
    simp only [Dec.isUnion]
    wp_auto
    iapply HΦ
    unfold isWFDecisionBnd
    iexists _
    iframe Hd
    isplitr
    · ipureintro; exact ⟨Hwf, Nat.le_refl _, Nat.le_refl _⟩
    iexact Hdn

end proof

end authorizer
end EtcdGrove
end Perennial
