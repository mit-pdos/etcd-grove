/-
Lean-first (no Rocq counterpart).

The proof of `(*Model).validateList`: the expected error (too large, other), the read's
consistency (`ListReadConsistency`), the output's too-large error that asks a retry, and by
consistency `equalListResponse` or the output list's resource version (`listResponseRV`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__validateList
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__equalListResponse
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__listResponseRV
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ListReadConsistency
public import Spec.k8s_io.apiserver.pkg.storage.IsTooLargeResourceVersion

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep k8s_etcd3
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
variable [errors_sem : _root_.Perennial.errors.Assumptions]
variable [storage_sem : k8s_io.apiserver.pkg.storage.Assumptions]
variable [apierrors_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

/-! `rvalidateListL`'s value on each path of `validateList`. -/

section listL
variable (x : Input) (m : RM) (exp out : RResp)

theorem listL_tl (h : isTooLargeE exp.err = true) :
    rvalidateListL x m exp out = (decide (out.obj = .nil) && isTooLargeE out.err) := by
  unfold rvalidateListL; simp [h]

theorem listL_deq (h1 : isTooLargeE exp.err = false) (hn : errNonNil exp.err = true) :
    rvalidateListL x m exp out = respEqL exp out := by
  unfold rvalidateListL; simp [h1, hn]

variable (he : exp.err = .deep .nil)
include he

theorem listL_none (hl : listConsL x = none) : rvalidateListL x m exp out = false := by
  unfold rvalidateListL; simp [he, hl, isTooLargeE, errNonNil]

variable (c : RCons) (r : w64) (hl : listConsL x = some (c, r))
include hl

theorem listL_retry
    (hc : (delayE out.err && decide (0 < uint.nat r) && decide (out.obj = .nil) && isTooLargeE out.err) = true) :
    rvalidateListL x m exp out = true := by
  unfold rvalidateListL; simp only [he, hl, show isTooLargeE (.deep .nil) = false from rfl, show errNonNil (.deep .nil) = false from rfl, hc, Bool.false_eq_true, ↓reduceIte]

variable (hc : (delayE out.err && decide (0 < uint.nat r) && decide (out.obj = .nil) && isTooLargeE out.err) = false)
include hc

theorem listL_cons (hcs : c = .consistent) : rvalidateListL x m exp out = equalListRespL x m exp out := by
  subst hcs
  unfold rvalidateListL; simp only [he, hl, show isTooLargeE (.deep .nil) = false from rfl, show errNonNil (.deep .nil) = false from rfl, hc, Bool.false_eq_true, ↓reduceIte]

theorem listL_exact (hcs : c = .exact) :
    rvalidateListL x m exp out = decide (listRespRVL out = some r) := by
  subst hcs
  unfold rvalidateListL; simp only [he, hl, show isTooLargeE (.deep .nil) = false from rfl, show errNonNil (.deep .nil) = false from rfl, hc, Bool.false_eq_true, ↓reduceIte]

theorem listL_not (hcs : c = .notOlderThan) :
    rvalidateListL x m exp out = ((listRespRVL out).map fun rr =>
      decide (uint.nat r ≤ uint.nat rr ∧ uint.nat rr ≤ uint.nat m.rv)).getD false := by
  subst hcs
  unfold rvalidateListL; simp only [he, hl, show isTooLargeE (.deep .nil) = false from rfl, show errNonNil (.deep .nil) = false from rfl, hc, Bool.false_eq_true, ↓reduceIte]
  cases hr : listRespRVL out <;> simp

end listL

theorem Model.validateList.wp_proof
    (wp_DE : reflect.DeepEqual.spec_k8s (GF := GF) (hG := hG))
    (wp_LRC : ListReadConsistency.spec (GF := GF) (hG := hG))
    (wp_ELR : Model.equalListResponse.spec (GF := GF) (hG := hG))
    (wp_LRV : Model.listResponseRV.spec (GF := GF) (hG := hG))
    (wp_IsTooLarge : storage.IsTooLargeResourceVersion.spec (GF := GF) (hG := hG))
    (wp_SCD : apierrors.SuggestsClientDelay.spec (GF := GF) (hG := hG))
    (wp_Unwrap : storage.StorageError.Unwrap.spec (GF := GF) (hG := hG)) :
    Model.validateList.spec (GF := GF) (hG := hG) := by
  intro mp m x re ro exp out hparse hfe hfo hle hlo
  cases re with | mk o1 e1 =>
  cases ro with | mk o2 e2 =>
  cases exp with | mk eo ee =>
  cases out with | mk oo oe =>
  simp only at hfe hfo hle hlo
  wp_start as ⟨#Hm, #Hre, #Hro⟩
  ihave #Hre0 := Hre
  ihave #Hro0 := Hro
  iunfold respRep at Hre
  iunfold respRep at Hro
  icases Hre with ⟨#Ho1, #He1⟩
  icases Hro with ⟨#Ho2, #He2⟩
  ihave #Hm0 := Hm
  unfold modelAt modelRep modelVal
  icases Hm with ⟨#Hinit, %il, %rl, %M, #Hp, -, -, -⟩
  iStructNamed Hp
  ihave %hn1 := errRep_nil_iff _ _ $$ He1
  ihave %hn2 := errRep_nil_iff _ _ $$ He2
  ihave %hm2 := deepRep_nil_iff _ _ _ $$ Ho2
  wp_auto
  cases e1 with
  | ok ii =>
    have hne1 : errNonNil ee = true := by
      cases h : errNonNil ee
      · exact absurd (hn1.2 h) nofun
      · rfl
    wp_auto
    ihave ⟨%w1, #Hw1, %hw1⟩ := errRep_apiErrAt wp_Unwrap _ ee hfe $$ He1
    wp_apply (wp_IsTooLarge _ w1) $$ [Hw1]
    · iexact Hw1
    rw [hw1]
    cases htl : isTooLargeE ee
    case true =>
      rw [listL_tl x m ⟨eo, ee⟩ ⟨oo, oe⟩ htl]
      wp_auto
      cases o2 with
      | ok io =>
        have hon : oo ≠ .nil := fun h => by have := hm2.2 h; cases this
        wp_auto
        simp only [hon, decide_false, Bool.false_and]
        iapply HΦ; itrivial
      | nil =>
        wp_auto
        ihave ⟨%w2, #Hw2, %hw2⟩ := errRep_apiErrAt wp_Unwrap _ oe hfo $$ He2
        wp_apply (wp_IsTooLarge _ w2) $$ [Hw2]
        · iexact Hw2
        simp only [hm2.1 rfl, _root_.decide_true, Bool.true_and, hw2]
        iapply HΦ; itrivial
    wp_auto
    have hde : deepErrE ee := by
      rcases ee with d | _ | _
      · trivial
      · cases htl
      · exact hfe.elim
    wp_apply (wp_DeepEqual_resp wp_DE _ _ _ _ eo oo ee oe hde hfo) $$ []
    · iframe Ho1 He1 Ho2 He2
    rw [listL_deq x m ⟨eo, ee⟩ ⟨oo, oe⟩ htl hne1]
    iapply HΦ; itrivial
  | nil =>
    have hee := errNonNil_false ee (hn1.1 rfl)
    wp_auto
    wp_apply (wp_LRC x hparse) $$ [] as %c %rv %ck %err %Hl
    · iexact Hinit
    rcases hlc : listConsL x with _ | ⟨cs, r⟩
    case none =>
      rw [hlc] at Hl
      cases err with
      | nil => exact absurd rfl Hl
      | ok ie =>
        wp_auto
        rw [listL_none x m ⟨eo, ee⟩ ⟨oo, oe⟩ hee hlc]
        iapply HΦ; itrivial
    rw [hlc] at Hl
    obtain ⟨rfl, hrv, rfl, rfl⟩ := Hl
    subst rv
    wp_auto
    wp_apply (wp_SCD _) $$ [] as %n2 %b2 #Hq
    · iapply errRep_apiErrOk wp_Unwrap _ oe hfo $$ He2
    ihave %hb2 : ⌜b2 = delayE oe⌝ $$ []
    · iapply errRep_delay wp_Unwrap _ oe hfo n2 b2
      iframe He2 Hq
    subst hb2
    ihave ⟨%w2, #Hw2, %hw2⟩ := errRep_apiErrAt wp_Unwrap _ oe hfo $$ He2
    wp_join (v := #(delayE oe && decide (0 < uint.nat r) && decide (oo = .nil) && isTooLargeE oe)) at
      (if: (if: (if: #(delayE oe) then _ else #false) then _ else #false) then _ else #false)
      with [reqRV output]
    · cases hd : delayE oe
      · wp_auto
        simp only [Bool.false_and]
        wp_join_done
      · wp_auto
        by_cases hr0 : 0 < uint.nat r
        · rw [decide_eq_true (show uint.Z (W64 0) < uint.Z r by word)]
          wp_auto
          cases o2 with
          | ok io =>
            have hon : oo ≠ .nil := fun h => by have := hm2.2 h; cases this
            wp_auto
            simp only [hon, decide_false, Bool.and_false, Bool.false_and]
            wp_join_done
          | nil =>
            wp_auto
            wp_apply (wp_IsTooLarge _ w2) $$ [Hw2]
            · iexact Hw2
            rw [hw2]
            simp only [hr0, hm2.1 rfl, _root_.decide_true, Bool.true_and]
            wp_join_done
        · rw [decide_eq_false (show ¬ uint.Z (W64 0) < uint.Z r by word)]
          wp_auto
          simp only [hr0, _root_.decide_false, Bool.true_and, Bool.false_and]
          wp_join_done
    cases hc : (delayE oe && decide (0 < uint.nat r) && decide (oo = .nil) && isTooLargeE oe)
    case true =>
      wp_auto
      rw [listL_retry x m ⟨eo, ee⟩ ⟨oo, oe⟩ hee cs r hlc hc]
      iapply HΦ; itrivial
    wp_auto
    cases cs
    case consistent =>
      simp only [rconsStr, _root_.decide_true]
      wp_auto
      have hde : deepErrE ee := by rw [hee]; trivial
      wp_apply (wp_ELR mp m x _ _ ⟨eo, ee⟩ ⟨oo, oe⟩ hle hlo hde hfo) $$ []
      · iframe Hre0 Hro0
        unfold modelAt modelRep modelVal
        iexact Hm0
      rw [listL_cons x m ⟨eo, ee⟩ ⟨oo, oe⟩ hee _ r hlc hc rfl]
      iapply HΦ; itrivial
    case exact =>
      simp only [rconsStr]
      wp_auto
      wp_apply (wp_LRV mp m _ ⟨oo, oe⟩ hlo) $$ []
      · iframe Hro0
        unfold modelAt modelRep modelVal
        iexact Hm0
      rw [listL_exact x m ⟨eo, ee⟩ ⟨oo, oe⟩ hee _ r hlc hc rfl]
      cases hr : listRespRVL ⟨oo, oe⟩ with
      | none =>
        simp only [hr, Option.isSome_none, Option.getD_none]
        wp_auto
        rw [show decide ((none : Option w64) = some r) = false by simp]
        iapply HΦ; itrivial
      | some rr =>
        simp only [hr, Option.isSome_some, Option.getD_some]
        wp_auto
        rw [show decide (some rr = some r) = decide (rr = r) by simp]
        iapply HΦ; itrivial
    case notOlderThan =>
      simp only [rconsStr]
      wp_auto
      wp_apply (wp_LRV mp m _ ⟨oo, oe⟩ hlo) $$ []
      · iframe Hro0
        unfold modelAt modelRep modelVal
        iexact Hm0
      rw [listL_not x m ⟨eo, ee⟩ ⟨oo, oe⟩ hee _ r hlc hc rfl]
      cases hr : listRespRVL ⟨oo, oe⟩ with
      | none =>
        simp only [hr, Option.isSome_none, Option.getD_none, Option.map_none]
        wp_auto
        iapply HΦ; itrivial
      | some rr =>
        simp only [hr, Option.isSome_some, Option.getD_some, Option.map_some]
        wp_auto
        have hmax : (#(functions go.max [go.uint64, go.uint64]) : val) = max.impl go.uint64 2 :=
          FuncUnfold.func_unfold (f := go.max) (type_args := List.replicate 2 go.uint64)
        simp only [hmax]
        wp_auto
        wp_if_destruct
        · wp_if_destruct
          · rw [show decide (uint.nat r ≤ uint.nat rr ∧ uint.nat rr ≤ uint.nat m.rv) =
                decide (uint.Z rr ≤ uint.Z m.rv) from by
              congr 1; apply propext; constructor
              · intro h; word
              · intro h; constructor <;> word]
            iapply HΦ; itrivial
          · rw [decide_eq_false (show ¬ (uint.nat r ≤ uint.nat rr ∧ uint.nat rr ≤ uint.nat m.rv) from
              fun h => by word)]
            iapply HΦ; itrivial
        · wp_if_destruct
          · rw [show decide (uint.nat r ≤ uint.nat rr ∧ uint.nat rr ≤ uint.nat m.rv) =
                decide (uint.Z rr ≤ uint.Z m.rv) from by
              congr 1; apply propext; constructor
              · intro h; word
              · intro h; constructor <;> word]
            iapply HΦ; itrivial
          · rw [decide_eq_false (show ¬ (uint.nat r ≤ uint.nat rr ∧ uint.nat rr ≤ uint.nat m.rv) from
              fun h => by word)]
            iapply HΦ; itrivial

end proof

end k8s_correctness
end EtcdGrove
end Perennial
