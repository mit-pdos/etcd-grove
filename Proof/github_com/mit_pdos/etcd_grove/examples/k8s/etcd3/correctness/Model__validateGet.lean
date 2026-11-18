/-
Lean-first (no Rocq counterpart).

The proof of `(*Model).validateGet`: the expected error's kind (too large, not found, other), the
output's error and object, the read's consistency, and for a stale read the output's resource
version.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__validateGet
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.GetReadConsistency
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner__ParseResourceVersion
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner__ObjectResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.IsNotFound
public import Spec.k8s_io.apiserver.pkg.storage.IsTooLargeResourceVersion
public import Spec.reflect.DeepEqualK8s

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

theorem errNonNil_false (e : RErr) (h : errNonNil e = false) : e = .deep .nil := by
  rcases e with d | _ | _ <;> simp [errNonNil] at h
  cases d <;> simp at h ⊢

theorem notFound_nonNil (e : RErr) (h : isNotFoundE e = true) : errNonNil e = true := by
  rcases e with d | _ | _ <;> simp [isNotFoundE] at h
  cases d <;> simp at h ⊢
  rfl

theorem notFound_shape (e : RErr) (h : isNotFoundE e = true) :
    ∃ k r i, e = .deep (.storageErr (W64 1) k r i) := by
  rcases e with d | _ | _ <;> simp [isNotFoundE] at h
  cases d <;> simp at h ⊢
  exact h

/-! `rvalidateGetL`'s value on each path of `validateGet`. -/

section getL
variable (x : Input) (m : RM) (exp out : RResp)

theorem getL_tl (h : isTooLargeE exp.err = true) :
    rvalidateGetL x m exp out = (decide (out.obj = .nil) && isTooLargeE out.err) := by
  unfold rvalidateGetL; simp [h]

theorem getL_deq (h1 : isTooLargeE exp.err = false) (hn : errNonNil exp.err = true)
    (hf : isNotFoundE exp.err = false) : rvalidateGetL x m exp out = respEqL exp out := by
  unfold rvalidateGetL; simp [h1, hn, hf]

variable (h1 : isTooLargeE exp.err = false) (h12 : (errNonNil exp.err && !isNotFoundE exp.err) = false)
include h1 h12

theorem getL_both (hn : errNonNil out.err = true) (ho : out.obj ≠ .nil) :
    rvalidateGetL x m exp out = false := by
  unfold rvalidateGetL; rw [h1, h12]; simp [hn, ho]

variable (h3 : (errNonNil out.err && decide (out.obj ≠ .nil)) = false)
include h3

theorem getL_cons (hmin : x.MinRV' = []) : rvalidateGetL x m exp out = respEqL exp out := by
  unfold rvalidateGetL; rw [h1, h12, h3]; simp [hmin]

variable (rv0 : w64) (hp : parseRVD x.MinRV' = some rv0) (hmin : x.MinRV' ≠ [])
include hp hmin

theorem getL_retry (hc : (delayE out.err && decide (0 < uint.nat rv0) && isTooLargeE out.err) = true) :
    rvalidateGetL x m exp out = true := by
  unfold rvalidateGetL; rw [h1, h12, h3]; simp only [hp, Option.getD_some, hc]; simp [hmin]

variable (hc : (delayE out.err && decide (0 < uint.nat rv0) && isTooLargeE out.err) = false)
include hc

theorem getL_nf (k : GoString) (r : w64) (i : DeepV) (he : out.err = .deep (.storageErr (W64 1) k r i)) :
    rvalidateGetL x m exp out =
      decide (0 < uint.nat r ∧ uint.nat rv0 ≤ uint.nat r ∧ uint.nat r ≤ uint.nat m.rv) := by
  unfold rvalidateGetL; rw [h1, h12, h3]; simp only [hp, Option.getD_some, hc]; simp [hmin, he]

theorem getL_nonNil (hn : errNonNil out.err = true) (hf : isNotFoundE out.err = false) :
    rvalidateGetL x m exp out = false := by
  unfold rvalidateGetL; rw [h1, h12, h3]; simp only [hp, Option.getD_some, hc]
  simp only [hmin, ↓reduceIte, Bool.false_eq_true]
  rcases hE : out.err with d | _ | _
  · cases d with
    | storageErr c k r i =>
      rw [hE] at hf; simp [isNotFoundE] at hf; simp [hf]
    | nil => rw [hE] at hn; cases hn
    | _ => rfl
  · rfl
  · rfl

theorem getL_obj (he : out.err = .deep .nil) (o : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj)
    (ho : out.obj = .obj o) :
    rvalidateGetL x m exp out = decide (uint.nat o.ResourceVersion' ≤ uint.nat m.rv) := by
  unfold rvalidateGetL; rw [h1, h12, h3]; simp only [hp, Option.getD_some, hc]; simp [hmin, he, ho]

theorem getL_nil (he : out.err = .deep .nil) (ho : out.obj = .nil) :
    rvalidateGetL x m exp out = false := by
  unfold rvalidateGetL; rw [h1, h12, h3]; simp only [hp, Option.getD_some, hc]; simp [hmin, he, ho]

end getL

-- The tail of `validateGet` (after the error checks): the resource version, the read's
-- consistency, the output's error and object.
set_option hygiene false in
local macro "get_tail" : tactic => `(tactic| (
  rw [hrv]
  wp_apply (wp_Parse x.MinRV') as %n %perr Hpr
  rw [hp]
  icases Hpr with %Hpr
  obtain ⟨rfl, hn⟩ := Hpr
  subst n
  wp_apply (wp_GRC opts)
  rw [hrv]
  by_cases hmin : x.MinRV' = []
  case pos =>
    simp only [hmin, ↓reduceIte, rconsStr, _root_.decide_true]
    wp_auto
    wp_apply (wp_DeepEqual_resp wp_DE _ _ _ _ eo oo ee oe hde hfo) $$ []
    · iframe Ho1 He1 Ho2 He2
    rw [getL_cons x m ⟨eo, ee⟩ ⟨oo, oe⟩ hT h12 h3 hmin]
    iapply HΦ; itrivial
  simp only [hmin, ↓reduceIte, rconsStr]
  wp_auto
  wp_apply (wp_SCD _) $$ [] as %n2 %b2 #Hq
  · iapply errRep_apiErrOk wp_Unwrap _ oe hfo $$ He2
  ihave %hb2 : ⌜b2 = delayE oe⌝ $$ []
  · iapply errRep_delay wp_Unwrap _ oe hfo n2 b2
    iframe He2 Hq
  subst hb2
  ihave ⟨%w2, #Hw2, %hw2⟩ := errRep_apiErrAt wp_Unwrap _ oe hfo $$ He2
  wp_join (v := #(delayE oe && decide (0 < uint.nat rv0) && isTooLargeE oe)) at
    (if: (if: #(delayE oe) then _ else #false) then _ else #false) with [reqRV output]
  · cases hd : delayE oe
    · wp_auto
      simp only [Bool.false_and]
      wp_join_done
    · wp_auto
      by_cases hr0 : 0 < uint.nat rv0
      · rw [decide_eq_true (show uint.Z (W64 0) < uint.Z rv0 by word)]
        wp_auto
        wp_apply (wp_IsTooLarge _ w2) $$ [Hw2]
        · iexact Hw2
        rw [hw2]
        simp only [hr0, _root_.decide_true, Bool.true_and]
        wp_join_done
      · rw [decide_eq_false (show ¬ uint.Z (W64 0) < uint.Z rv0 by word)]
        wp_auto
        simp only [hr0, _root_.decide_false, Bool.true_and, Bool.false_and]
        wp_join_done
  cases hc : (delayE oe && decide (0 < uint.nat rv0) && isTooLargeE oe)
  case true =>
    wp_auto
    rw [getL_retry x m ⟨eo, ee⟩ ⟨oo, oe⟩ hT h12 h3 rv0 hp hmin hc]
    iapply HΦ; itrivial
  wp_auto
  ihave #Hc2 := errRep_codeAt _ oe hfo $$ He2
  wp_apply (wp_IsNotFound _ DFrac.discard (codeE oe)) $$ [Hc2] as -
  · iexact Hc2
  rw [← isNotFoundE_codeE]
  cases hnf2 : isNotFoundE oe
  case true =>
    obtain ⟨k, r, i, hoe⟩ := notFound_shape oe hnf2
    rw [getL_nf x m ⟨eo, ee⟩ ⟨oo, oe⟩ hT h12 h3 rv0 hp hmin hc k r i hoe]
    subst hoe
    iunfold errRep at He2
    iunfold deepRO at He2
    iunfold deepRep at He2
    icases He2 with ⟨%p, %ie, %he, #Hpe, -⟩
    simp only [interface.mkOk] at he
    cases he
    all_goals (
      wp_auto
      iStructNamed Hpe
      wp_auto
      wp_if_destruct
      · wp_if_destruct
        · rw [show decide (0 < uint.nat r ∧ uint.nat rv0 ≤ uint.nat r ∧ uint.nat r ≤ uint.nat m.rv) =
              decide (uint.Z r ≤ uint.Z m.rv) from by
            congr 1; apply propext; constructor
            · intro h; word
            · intro h; refine ⟨?_, ?_, ?_⟩ <;> word]
          iapply HΦ; itrivial
        · rw [decide_eq_false (show ¬ (0 < uint.nat r ∧ uint.nat rv0 ≤ uint.nat r ∧
              uint.nat r ≤ uint.nat m.rv) from fun h => by word)]
          iapply HΦ; itrivial
      · rw [decide_eq_false (show ¬ (0 < uint.nat r ∧ uint.nat rv0 ≤ uint.nat r ∧
            uint.nat r ≤ uint.nat m.rv) from fun h => by word)]
        iapply HΦ; itrivial)
  wp_auto))

-- The end of the tail when the output's error is nil: its object.
set_option hygiene false in
local macro "get_end_nil" : tactic => `(tactic| (
  obtain rfl := errNonNil_false oe hE2
  cases o2 with
  | nil =>
    wp_auto
    rw [getL_nil x m ⟨eo, _⟩ ⟨oo, _⟩ hT h12 h3 rv0 hp hmin hc rfl (hm2.1 rfl)]
    iapply HΦ; itrivial
  | ok io =>
    have hon : oo ≠ .nil := fun h => by have := hm2.2 h; cases this
    obtain ⟨o, rfl⟩ : ∃ o, oo = .obj o := by
      cases oo with
      | nil => exact absurd rfl hon
      | obj o => exact ⟨o, rfl⟩
      | _ => exact hoo.elim
    iunfold deepRO at Ho2
    iunfold deepRep at Ho2
    icases Ho2 with ⟨%po, %hpo, #Hpo⟩
    cases hpo
    wp_auto
    wp_apply (wp_ORV po DFrac.discard o) $$ [Hpo] as -
    · iexact Hpo
    rw [getL_obj x m ⟨eo, _⟩ ⟨_, _⟩ hT h12 h3 rv0 hp hmin hc rfl o rfl,
      show decide (uint.nat o.ResourceVersion' ≤ uint.nat m.rv) =
        decide (uint.Z o.ResourceVersion' ≤ uint.Z m.rv) from by
      congr 1; apply propext; constructor <;> intro h <;> word]
    iapply HΦ; itrivial))

-- After the expected error's checks: the output not both an error and an object.
set_option hygiene false in
local macro "get_mid" : tactic => `(tactic| (
  cases e2 with
  | ok ie =>
    have hne2 : errNonNil oe = true := by
      cases h : errNonNil oe
      · exact absurd (hn2.2 h) nofun
      · rfl
    wp_auto
    cases o2 with
    | ok io =>
      have hon : oo ≠ .nil := fun h => by have := hm2.2 h; cases this
      wp_auto
      rw [getL_both x m ⟨eo, ee⟩ ⟨oo, oe⟩ hT h12 hne2 hon]
      iapply HΦ; itrivial
    | nil =>
      have h3 : (errNonNil oe && decide (oo ≠ .nil)) = false := by simp [hm2.1 rfl]
      wp_auto
      get_tail
      rw [getL_nonNil x m ⟨eo, ee⟩ ⟨oo, oe⟩ hT h12 h3 rv0 hp hmin hc hne2 hnf2]
      iapply HΦ; itrivial
  | nil =>
    have hE2 : errNonNil oe = false := hn2.1 rfl
    have h3 : (errNonNil oe && decide (oo ≠ .nil)) = false := by simp [hE2]
    wp_auto
    get_tail
    get_end_nil))

theorem Model.validateGet.wp_proof
    (wp_DE : reflect.DeepEqual.spec_k8s (GF := GF) (hG := hG))
    (wp_Parse : k8s_etcd3.versioner.ParseResourceVersion.spec (GF := GF) (hG := hG))
    (wp_ORV : k8s_etcd3.versioner.ObjectResourceVersion.spec (GF := GF) (hG := hG))
    (wp_GRC : GetReadConsistency.spec (GF := GF) (hG := hG))
    (wp_IsNotFound : storage.IsNotFound.spec (GF := GF) (hG := hG))
    (wp_IsTooLarge : storage.IsTooLargeResourceVersion.spec (GF := GF) (hG := hG))
    (wp_SCD : apierrors.SuggestsClientDelay.spec (GF := GF) (hG := hG))
    (wp_Unwrap : storage.StorageError.Unwrap.spec (GF := GF) (hG := hG)) :
    Model.validateGet.spec (GF := GF) (hG := hG) := by
  intro mp m x opts re ro exp out hrv hparse hfe hfo hoo
  cases re with | mk o1 e1 =>
  cases ro with | mk o2 e2 =>
  cases exp with | mk eo ee =>
  cases out with | mk oo oe =>
  simp only at hfe hfo hoo
  obtain ⟨rv0, hp⟩ := Option.isSome_iff_exists.1 hparse
  wp_start as ⟨#Hm, #Hre, #Hro⟩
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
    wp_apply (wp_IsTooLarge _ w1) $$ [$Hw1]
    rw [hw1]
    cases htl : isTooLargeE ee
    case true =>
      rw [getL_tl x m ⟨eo, ee⟩ ⟨oo, oe⟩ htl]
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
    ihave #Hc1 := errRep_codeAt _ ee hfe $$ He1
    wp_apply (wp_IsNotFound _ DFrac.discard (codeE ee)) $$ [$Hc1] as -
    rw [← isNotFoundE_codeE]
    cases hnf : isNotFoundE ee
    case false =>
      wp_auto
      have hde : deepErrE ee := by
        rcases ee with d | _ | _
        · trivial
        · cases htl
        · exact hfe.elim
      wp_apply (wp_DeepEqual_resp wp_DE o1 _ o2 e2 eo oo ee oe hde hfo) $$ []
      · iframe Ho1 He1 Ho2 He2
      rw [getL_deq x m ⟨eo, ee⟩ ⟨oo, oe⟩ htl hne1 hnf]
      iapply HΦ; itrivial
    wp_auto
    have hT := htl
    have h12 : (errNonNil ee && !isNotFoundE ee) = false := by simp [hnf]
    have hde : deepErrE ee := by
      obtain ⟨k, r, i, h⟩ := notFound_shape ee hnf
      rw [h]; trivial
    get_mid
  | nil =>
    have hE : errNonNil ee = false := hn1.1 rfl
    have hee := errNonNil_false ee hE
    have hT : isTooLargeE ee = false := by rw [hee]; rfl
    have h12 : (errNonNil ee && !isNotFoundE ee) = false := by simp [hE]
    have hde : deepErrE ee := by rw [hee]; trivial
    wp_auto
    get_mid

end proof

end k8s_correctness
end EtcdGrove
end Perennial
