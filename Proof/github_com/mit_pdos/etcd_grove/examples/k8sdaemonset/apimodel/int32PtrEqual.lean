/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/apimodel/int32PtrEqual.lean`.
Lean-first.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.int32PtrEqual
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.ObjLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.MapLemmas

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem int32PtrEqual.wp_proof : int32PtrEqual.spec (GF := GF) (hG := hG) := by
  intro _ a b da db
  wp_start as ⟨Ha, Hb⟩
  icases ownPtrD_null _ _ _ _ $$ Ha with ⟨Ha, %ha⟩
  icases ownPtrD_null _ _ _ _ $$ Hb with ⟨Hb, %hb⟩
  wp_auto
  rcases da with _ | x <;> rcases db with _ | y <;> simp only [iff_true, iff_false, reduceCtorEq] at ha hb
  · subst ha hb
    wp_auto
    rw [decide_eq_true rfl]
    iapply HΦ
    iframe
  · subst ha
    (try wp_auto)
    (try rw [decide_eq_false hb])
    (try wp_auto)
    rw [decide_eq_false (by simp)]
    iapply HΦ
    iframe
  · subst hb
    rw [decide_eq_false ha]
    wp_auto
    rw [decide_eq_false ha]
    wp_auto
    rw [decide_eq_false (by simp)]
    iapply HΦ
    iframe
  · rw [decide_eq_false ha]
    wp_auto
    rw [decide_eq_false hb]
    wp_auto
    ihave Ha := (ownPtrD_base_some _ _ _).1 $$ Ha
    ihave Hb := (ownPtrD_base_some _ _ _).1 $$ Hb
    wp_auto
    ihave Ha := (ownPtrD_base_some _ _ _).2 $$ Ha
    ihave Hb := (ownPtrD_base_some _ _ _).2 $$ Hb
    simp only [Option.some.injEq]
    iapply HΦ
    iframe

end proof

end apimodel
end EtcdGrove
end Perennial
