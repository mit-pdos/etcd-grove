module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.failureFree

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_correctness
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- An operation passes `failureFree`'s test (on any boxes of it). -/
abbrev opGood (o : github_com.anishathalye.porcupine.Operation) : Prop :=
  ∀ x y, o.Input' = boxIn x → o.Output' = boxOut y → okOut x y = true

include sem package_sem in
theorem opGood_box (o : github_com.anishathalye.porcupine.Operation) (x : Input) (y : Output)
    (hx : o.Input' = boxIn x) (hy : o.Output' = boxOut y) : opGood o ↔ okOut x y = true := by
  constructor
  · intro h; exact h x y hx hy
  · intro h x' y' hx' hy'
    have e1 : x = x' := Input_intoVal_inj (sem := sem) (package_sem := package_sem)
      (GoInterfaceOk.mk.inj (GoInterface.ok.inj (hx.symm.trans hx'))).2
    have e2 : y = y' := Output_intoVal_inj (sem := sem) (package_sem := package_sem)
      (GoInterfaceOk.mk.inj (GoInterface.ok.inj (hy.symm.trans hy'))).2
    subst e1 e2; exact h

theorem failureFree.wp_proof : failureFree.spec (GF := GF) (hG := hG) := by
  intro sl ops dq Hbox
  wp_start as Hs
  ihave %Hl := ownSlice_len $$ Hs
  wp_auto
  ihave HI : (∃ (j : w64) (opv : github_com.anishathalye.porcupine.Operation),
      "i" ∷ i_ptr ↦ j ∗ "op" ∷ op_ptr ↦ opv ∗ "Hs" ∷ sl ↦*{dq} ops ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧ ∀ o ∈ ops.take (sint.nat j), opGood o⌝ : IProp GF)
    $$ [i op Hs]
  · iexists W64 0, _
    iframe
    ipureintro; refine ⟨by word, by word, ?_⟩
    intro o ho
    simp [show sint.nat (0#64 : w64) = 0 from rfl] at ho
  wp_for HI
  wp_if_destruct
  · have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len :=
      ⟨Hj.1, by first | exact Hif | exact dec_true Hif⟩
    list_elem ops (sint.nat j) as o
    simp only [Hb', _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z j) ops _ o Hj.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Ho_lookup
    obtain ⟨x, y, hx, hy⟩ := Hbox o (List.mem_of_getElem? Ho_lookup)
    have hgood := opGood_box (sem := sem) (package_sem := package_sem) o x y hx hy
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
      have := Hb'.1; have := Hb'.2; have := Hl.2; word
    have hstep : ∀ (h : opGood o), ∀ o' ∈ ops.take (sint.nat (j + W64 1)), opGood o' := by
      intro h o' ho'
      rw [hj1, List.take_add_one, Ho_lookup] at ho'
      simp only [List.mem_append, Option.toList_some, List.mem_singleton] at ho'
      rcases ho' with ho' | rfl
      · exact Hj.2.2 o' ho'
      · exact h
    have hfail : ∀ (h : ¬ opGood o), ¬ ∀ o' ∈ ops, opGood o' :=
      fun h hall => h (hall o (List.mem_of_getElem? Ho_lookup))
    simp only [hx]
    wp_auto
    (try simp only [hy])
    (try wp_auto)
    wp_if_destruct
    · -- a watch
      cases hs : x.Skip'
      · simp only [Bool.not_false]
        wp_auto
        cases hw : y.WFailed'
        · (try wp_auto)
          wp_for_post
          iframe
          iexists j + W64 1, _
          iframe
          ipureintro
          refine ⟨by word, by word, hstep ?_⟩
          rw [hgood]
          simp_all [okOut]
        · (try wp_auto)
          wp_for_post
          iapply HΦ
          iframe
          ipureintro
          simp only [Bool.false_eq_true, false_iff]
          apply hfail
          rw [hgood]
          simp_all [okOut]
      · simp only [Bool.not_true]
        wp_auto
        wp_for_post
        iframe
        iexists j + W64 1, _
        iframe
        ipureintro
        refine ⟨by word, by word, hstep ?_⟩
        rw [hgood]
        simp_all [okOut]
    · wp_if_destruct
      · wp_for_post
        iapply HΦ
        iframe
        ipureintro
        simp only [Bool.false_eq_true, false_iff]
        apply hfail
        rw [hgood]
        simp_all [okOut]
      · wp_for_post
        iframe
        iexists j + W64 1, _
        iframe
        ipureintro
        refine ⟨by word, by word, hstep ?_⟩
        rw [hgood]
        simp_all [okOut]
  · have hge : ¬ sint.Z j < sint.Z sl.len := by first | exact Hif | exact dec_false Hif
    (try rw [decide_eq_false hge, if_pos (decide_eq_true rfl)])
    (try wp_auto)
    iapply HΦ
    iframe
    ipureintro
    have hfull : ops.take (sint.nat j) = ops := List.take_of_length_le (by word)
    rw [hfull] at Hj
    simp only [true_iff]
    exact Hj.2.2

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
