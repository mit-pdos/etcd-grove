/-
Lean-first (no Rocq counterpart).

The proof of `step`: by the error, `isWrite` and `outEqual`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.step
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.isWrite
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.mstep
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.outEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

set_option hygiene false in
/-- `step` returns `nil` (`stepL g x y = []`, proved by `h`). -/
local macro "step_nil" h:term : tactic => `(tactic| (
  rw [show stepL g x y = [] from $h]
  ihave Hn := ownSlice_nil (V := mcfg) (GF := GF) (DFrac.own 1)
  iapply HΦ
  isplitl [Hn]
  · iexact Hn
  · iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF)).2
    iempintro))

theorem step.wp_proof (wp_isWrite : isWrite.spec (GF := GF) (hG := hG))
    (wp_mstep : mstep.spec (GF := GF) (hG := hG))
    (wp_outEqual : outEqual.spec (GF := GF) (hG := hG)) :
    step.spec (GF := GF) (hG := hG) := by
  intro c g x y
  wp_start as ⟨#Hc, %Hb⟩
  unfold cfgOwn
  icases Hc with ⟨#Hcs, #Hcp⟩
  ihave %Hlp := ownSlice_len $$ Hcp
  wp_auto
  by_cases hE : y.Err' ≠ W64 4
  · -- no error: `mstep`, then `outEqual`
    rw [show decide (y.Err' = W64 4) = false by simpa using hE]
    try wp_auto
    wp_apply wp_mstep x c.st' g.st $$ [$Hcs] as %s' %o ⟨#Hs', %Ho⟩
    · ipureintro; exact Hb.1
    subst Ho
    wp_apply wp_outEqual y (mstepL x g.st).2
    cases hq : decide (y = (mstepL x g.st).2)
    · try wp_auto
      step_nil (by
        rw [stepL, ite_cond_eq_false _ _ (eq_false hE),
          ite_cond_eq_false _ _ (eq_false (of_decide_eq_false hq))])
    · try wp_auto
      wp_apply wp_slice_literal (l := [(⟨s', c.pend'⟩ : mcfg)])
      isplitr
      · ipureintro; rfl
      iintro %lsl ⟨Hl1, _⟩
      wp_auto
      iapply HΦ
      rw [show stepL g x y = [⟨(mstepL x g.st).1, g.pend⟩] by
        rw [stepL, ite_cond_eq_false _ _ (eq_false hE), ite_cond_eq_true _ _ (eq_true (of_decide_eq_true hq))]]
      iframe
      iapply (BigSepL2.bigSepL2_singleton (PROP := IProp GF)).2
      isplit
      · iexact Hs'
      · iexact Hcp
  · rw [show decide (y.Err' = W64 4) = true by simpa using hE]
    try wp_auto
    wp_apply wp_isWrite x
    cases hw : isWriteL x
    · -- a failed read: `c`
      try wp_auto
      wp_apply wp_slice_literal (l := [c])
      isplitr
      · ipureintro; rfl
      iintro %lsl ⟨Hl1, _⟩
      wp_auto
      iapply HΦ
      rw [show stepL g x y = [g] by rw [stepL, if_pos (Decidable.of_not_not hE)]; simp [hw]]
      iframe
      iapply (BigSepL2.bigSepL2_singleton (PROP := IProp GF)).2
      isplit
      · iexact Hcs
      · iexact Hcp
    · -- a failed write: pending
      try wp_auto
      wp_apply wp_slice_make3 (V := Input) (W64 0) (c.pend'.len + W64 1) ⟨by word, by word⟩
        as %o0 ⟨Ho, Hocap, -⟩
      rw [List.replicate_zero]
      wp_apply wp_slice_literal (l := [x])
      isplitr
      · ipureintro; rfl
      iintro %lsl ⟨Hl1, _⟩
      wp_apply wp_slice_append $$ [$Ho $Hocap $Hl1] as %o1 ⟨Ho, Hocap, -⟩
      wp_apply +noauto wp_slice_append $$ [$Ho $Hocap $Hcp] as %o2 ⟨Ho, Hocap, -⟩
      rw [List.nil_append, List.singleton_append]
      ipersist Ho
      wp_auto
      wp_apply wp_slice_literal (l := [(⟨c.st', o2⟩ : mcfg)])
      isplitr
      · ipureintro; rfl
      iintro %lsl2 ⟨Hl2, _⟩
      wp_auto
      iapply HΦ
      rw [show stepL g x y = [⟨g.st, x :: g.pend⟩] by rw [stepL, if_pos (Decidable.of_not_not hE)]; simp [hw]]
      iframe
      iapply (BigSepL2.bigSepL2_singleton (PROP := IProp GF)).2
      isplit
      · iexact Hcs
      · iexact Ho

end proof

end k8setcd3
end EtcdGrove
end Perennial
