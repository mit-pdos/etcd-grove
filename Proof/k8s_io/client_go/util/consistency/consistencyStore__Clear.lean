/-
Proof of `Spec/k8s_io/client_go/util/consistency/consistencyStore__Clear.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.consistency.consistencyStore__Clear
public import Proof.k8s_io.client_go.util.consistency.InvLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.consistency

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

theorem consistencyStore.Clear.wp_proof :
    consistencyStore.Clear.spec (GF := GF) (hG := hG) := by
  intro c γ T S G o uid md
  iintro %Φ ⟨#Hpkg, #Hc, Hpre⟩ HAU
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hc' := Hc
  iNamed Hc'
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply (lc := 3) sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hwl, HP⟩
  iunfold writesP at HP
  icases HP with ⟨%W, Hm, Hg⟩
  wp_apply wp_map_lookup1 $$ [$Hm] as Hm
  cases hw : W !! o with
  | none =>
    simp only [Option.getD_none]
    wp_auto
    cases md with
    | none =>
      unfold clearState clearPost at *
      ihave HAU : auClear γ o uid iprop(True -∗ Φ #()) $$ [HAU]
      · iunfold auClear; inext; iexact HAU
      imod clear_keep_commit γ T (1 : Qp).half iprop(True -∗ Φ #())
        $$ [$Hinv $Hlc2 $Hlc3 $Hg $HAU] with ⟨Hg, HK⟩
      · ileft; ipureintro; exact hw
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hm Hg]
      · iunfold writesP; iexists W; iframe
      iapply HK; itrivial
    | some e =>
      obtain ⟨r, s, V⟩ := e
      unfold clearState clearPost clearPre at *
      icases Hpre with ⟨Htok, #Hrec, %Hs⟩
      imod ens_clear_commit γ T $$ [$Hinv $Hlc2 $Htok $Hg] with ⟨Hg, HT⟩
      rw [delete_none W o hw]
      imod fire_trivial _ $$ HAU with HK
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hm Hg]
      · iunfold writesP; iexists W; iframe
      iapply HK $$ HT
  | some r1 =>
    simp only [Option.getD_some]
    imod lookup_rec γ T _ hw $$ [$Hinv $Hlc1 $Hg] with ⟨Hg, %s1, #Hrec, %ho⟩
    ihave #Hrec' := Hrec
    iunfold isRec at Hrec'
    icases Hrec' with ⟨-, Hp⟩
    iunfold recPhys at Hp
    icases Hp with ⟨%Hnn, #Huid, -, -⟩
    simp only [decide_eq_false Hnn, Bool.not_false]
    wp_auto
    wp_func_call
    wp_call
    by_cases hl : uid.length < 2 ^ 63
    case neg => rw [if_neg hl]; wp_apply wp_AngelicExit
    rw [if_pos hl]
    wp_auto
    have hlen : (W64 (uid.length : Int) = W64 0) ↔ uid = [] := by
      constructor
      · intro h
        have : uid.length = 0 := by word
        exact List.eq_nil_of_length_eq_zero this
      · intro h; subst h; rfl
    by_cases he : uid = []
    · simp only [hlen.2 he, _root_.decide_true]
      have HC : uid = [] ∨ s1.uid = uid := Or.inl he
      wp_auto
      wp_apply wp_mapDelete $$ [$Hm] as Hm
      cases md with
      | none =>
        unfold clearState clearPost at *
        ihave HAU : auClear γ o uid iprop(True -∗ Φ #()) $$ [HAU]
        · iunfold auClear; inext; iexact HAU
        imod clear_del_commit γ T iprop(True -∗ Φ #()) hw HC
          $$ [$Hinv $Hlc2 $Hlc3 $Hg $Hrec $HAU] with ⟨Hg, HK⟩
        wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hm Hg]
        · iunfold writesP; iexists _; iframe
        iapply HK; itrivial
      | some e =>
        obtain ⟨r, s, V⟩ := e
        unfold clearState clearPost clearPre at *
        icases Hpre with ⟨Htok, #Hrec2, %Hs⟩
        imod ens_clear_commit γ T $$ [$Hinv $Hlc2 $Htok $Hg] with ⟨Hg, HT⟩
        imod fire_trivial _ $$ HAU with HK
        wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hm Hg]
        · iunfold writesP; iexists _; iframe
        iapply HK $$ HT
    · simp only [show ¬ (W64 (uid.length : Int) = W64 0) from fun h => he (hlen.1 h), decide_false]
      wp_auto
      by_cases hu : s1.uid = uid
      · simp only [hu, _root_.decide_true]
        have HC : uid = [] ∨ s1.uid = uid := Or.inr hu
        wp_auto
        wp_apply wp_mapDelete $$ [$Hm] as Hm
        cases md with
        | none =>
          unfold clearState clearPost at *
          ihave HAU : auClear γ o uid iprop(True -∗ Φ #()) $$ [HAU]
          · iunfold auClear; inext; iexact HAU
          imod clear_del_commit γ T iprop(True -∗ Φ #()) hw HC
            $$ [$Hinv $Hlc2 $Hlc3 $Hg $Hrec $HAU] with ⟨Hg, HK⟩
          wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hm Hg]
          · iunfold writesP; iexists _; iframe
          iapply HK; itrivial
        | some e =>
          obtain ⟨r, s, V⟩ := e
          unfold clearState clearPost clearPre at *
          icases Hpre with ⟨Htok, #Hrec2, %Hs⟩
          imod ens_clear_commit γ T $$ [$Hinv $Hlc2 $Htok $Hg] with ⟨Hg, HT⟩
          imod fire_trivial _ $$ HAU with HK
          wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hm Hg]
          · iunfold writesP; iexists _; iframe
          iapply HK $$ HT
      · simp only [hu, decide_false]
        wp_auto
        cases md with
        | none =>
          unfold clearState clearPost at *
          ihave HAU : auClear γ o uid iprop(True -∗ Φ #()) $$ [HAU]
          · iunfold auClear; inext; iexact HAU
          imod clear_keep_commit γ T (1 : Qp).half iprop(True -∗ Φ #())
            $$ [$Hinv $Hlc2 $Hlc3 $Hg $HAU] with ⟨Hg, HK⟩
          · iright; iexists r1, s1; iframe #; ipureintro
            exact ⟨hw, fun h => h.elim he hu⟩
          wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hm Hg]
          · iunfold writesP; iexists W; iframe
          iapply HK; itrivial
        | some e =>
          obtain ⟨r, s, V⟩ := e
          unfold clearState clearPost clearPre at *
          icases Hpre with ⟨Htok, #Hrec2, %Hs⟩
          imod ens_clear_info γ T (1 : Qp).half $$ [$Hinv $Hlc2 $Htok $Hg] with ⟨Htok, Hg, %Hwr⟩
          rw [hw] at Hwr
          rcases Hwr with Hwr | Hwr
          · cases Hwr
            ihave %Hss := isRec_agree γ (r := r1) (s := s1) (s' := s) $$ [$Hrec $Hrec2]
            subst Hss
            exact absurd Hs.2 hu
          · cases Hwr

end proof

end consistency
end EtcdGrove
end Perennial
