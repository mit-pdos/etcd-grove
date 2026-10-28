/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/podGrace.lean`.
Lean-first: the grace period read off the options or the pod (`PodLemmas.lean`), as `podGraceD`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.podGrace
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.PodLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apimodel

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8sdaemonset

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : apimodel.Assumptions]

set_option hygiene false in
/-- `podGrace`'s second `if`: the node name and the phase. -/
macro "pg_split" : tactic => `(tactic| (
  by_cases hn : d.Spec'.NodeName' = [] <;> simp only [hn, decide_true, decide_false] <;> (try wp_auto) <;> (try simp only [hP]) <;>
  by_cases hf : d.Status'.Phase' = go!"Failed" <;> (try simp only [hf, decide_true, decide_false]) <;> (try wp_auto) <;> (try simp only [hP]) <;>
  by_cases hs : d.Status'.Phase' = go!"Succeeded" <;> (try simp only [hs, decide_true, decide_false]) <;> (try wp_auto)
  ))

set_option hygiene false in
/-- The common end of `podGrace`'s branches: the pod and the options back. -/
macro "pg_fin" : tactic => `(tactic| (
  iapply HΦ
  iframe Ho
  iunfold objAt
  iexists l
  isplitr
  · ipureintro; rfl
  iunfold podAt
  iexists v
  iframe))

theorem podGrace.wp_proof : podGrace.spec (GF := GF) (hG := hG) := by
  intro _ x d opts dq dop
  wp_start as ⟨Hx, Ho⟩
  iunfold objAt at Hx
  icases Hx with ⟨%l, %hx, Hl⟩
  subst hx
  iunfold podAt at Hl
  icases Hl with ⟨%v, Hl, Hd⟩
  icases pod_grace_facts _ _ _ $$ Hd with ⟨Hd, %Hf⟩
  icases delopts_gps_null _ _ _ $$ Ho with ⟨Ho, %Hg⟩
  obtain ⟨hN, hP, hT⟩ := Hf
  wp_auto
  by_cases hgn : opts.GracePeriodSeconds' = null
  · have hgps : dop.GracePeriodSeconds' = none := Hg.mp hgn
    simp only [decide_eq_true hgn, Bool.not_true]
    (try wp_auto)
    cases ht : d.Spec'.TerminationGracePeriodSeconds' with
    | none =>
      have htn : v.Spec'.TerminationGracePeriodSeconds' = null := hT.mpr ht
      simp only [htn, decide_true, Bool.not_true]
      (try wp_auto)
      (try simp only [k8s_io.api.core.v1.PodFailed, k8s_io.api.core.v1.PodSucceeded])
      (try simp only [hN, hP])
      pg_split <;>
      (try simp only [podGraceD, hgps, ht, Option.getD_none, hn, hf, hs, true_or, or_true, or_false, false_or, ite_true, ite_false, ↓reduceIte]) <;>
      (try rw [show (zero_val w64 : w64) = W64 0 from rfl]) <;>
      (try rw [if_neg (show ¬ sint.Z (W64 0) < 0 by simp)]) <;>
      pg_fin
    | some g =>
      have htn : v.Spec'.TerminationGracePeriodSeconds' ≠ null := fun h => by rw [hT.mp h] at ht; cases ht
      simp only [decide_eq_false htn, Bool.not_false]
      icases pod_tgps_acc _ _ _ g ht $$ Hd with ⟨Hpt, Hd⟩
      (try wp_auto)
      ihave Hd := Hd $$ Hpt
      (try simp only [k8s_io.api.core.v1.PodFailed, k8s_io.api.core.v1.PodSucceeded])
      (try simp only [hN, hP])
      have hz : sint.Z (W64 0) = 0 := by simp
      pg_split <;>
      (try (by_cases hneg : sint.Z g < 0 <;> simp only [hz, hneg, decide_true, decide_false] <;> (try wp_auto))) <;>
      (try simp only [podGraceD, hgps, ht, Option.getD_none, Option.getD_some, hn, hf, hs, _root_.or_self, _root_.or_false, _root_.false_or, _root_.true_or, _root_.or_true, ↓reduceIte, hz, Int.lt_irrefl]) <;>
      (try simp only [hneg, ↓reduceIte]) <;>
      pg_fin
  · obtain ⟨g, hgps⟩ : ∃ g, dop.GracePeriodSeconds' = some g := by
      cases h : dop.GracePeriodSeconds' with
      | none => exact absurd (Hg.mpr h) hgn
      | some g => exact ⟨g, rfl⟩
    simp only [decide_eq_false hgn, Bool.not_false]
    icases delopts_gps_acc _ _ _ g hgps $$ Ho with ⟨Hpt, Ho⟩
    (try wp_auto)
    ihave Ho := Ho $$ Hpt
    (try simp only [k8s_io.api.core.v1.PodFailed, k8s_io.api.core.v1.PodSucceeded])
    (try simp only [hN, hP])
    have hz : sint.Z (W64 0) = 0 := by simp
    pg_split <;>
    (try (by_cases hneg : sint.Z g < 0 <;> simp only [hz, hneg, decide_true, decide_false] <;> (try wp_auto))) <;>
    (try simp only [podGraceD, hgps, Option.getD_some, hn, hf, hs, _root_.or_self, _root_.or_false, _root_.false_or, _root_.true_or, _root_.or_true, ↓reduceIte, hz, Int.lt_irrefl]) <;>
    (try simp only [hneg, ↓reduceIte]) <;>
    pg_fin

end proof

end apimodel
end EtcdGrove
end Perennial
