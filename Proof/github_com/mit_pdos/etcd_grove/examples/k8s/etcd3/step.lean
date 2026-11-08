/-
Lean-first (no Rocq counterpart).

The proof of `step`: by the error, `isWrite` and `outEqual`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.step
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.isWrite
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.mstep
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.outEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.mlist
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.advance

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

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
    (wp_outEqual : outEqual.spec (GF := GF) (hG := hG))
    (wp_mlist : mlist.spec (GF := GF) (hG := hG))
    (wp_advance : advance.spec (GF := GF) (hG := hG)) :
    step.spec (GF := GF) (hG := hG) := by
  intro c g x y
  wp_start as ⟨#Hc, %Hb⟩
  ihave #Hc' : cfgOwn (GF := GF) c g $$ [Hc]
  · iexact Hc
  isimp only [cfgOwn] at Hc'
  icases Hc' with ⟨#Hcs, #Hch, #Hcp, %Hhl⟩
  ihave %Hlp := ownSlice_len $$ Hcp
  wp_auto
  by_cases hE : y.Err' ≠ W64 4
  · rw [show decide (y.Err' = W64 4) = false by simpa using hE]
    try wp_auto
    by_cases hK : x.Kind' = W64 4
    · -- a list: `mlist`, then `outEqual`
      have hks : kstepL x g.st = (g.st, mlistL x g.st) := by unfold kstepL; rw [if_pos hK]
      rw [show decide (x.Kind' = W64 4) = true by simpa using hK]
      try wp_auto
      wp_apply wp_mlist x c g $$ [$Hc]
      wp_apply wp_outEqual y (mlistL x g.st)
      cases hq : decide (y = mlistL x g.st)
      · try wp_auto
        step_nil (by
          rw [stepL, ite_cond_eq_false _ _ (eq_false hE), hks,
            ite_cond_eq_false _ _ (eq_false (of_decide_eq_false hq))])
      · try wp_auto
        wp_apply wp_slice_literal (l := [c])
        isplitr
        · ipureintro; rfl
        iintro %lsl ⟨Hl1, _⟩
        wp_auto
        iapply HΦ
        rw [show stepL g x y = [g] by
          rw [stepL, ite_cond_eq_false _ _ (eq_false hE), hks,
            ite_cond_eq_true _ _ (eq_true (of_decide_eq_true hq))]]
        iframe
        iapply (BigSepL2.bigSepL2_singleton (PROP := IProp GF)).2
        iexact Hc
    · -- any other call: `mstep`, then `outEqual`, then `advance`
      have hks : kstepL x g.st = (advanceL g.st (mstepL x g.st.st).1, (mstepL x g.st.st).2) := by
        unfold kstepL; rw [if_neg hK]
      rw [show decide (x.Kind' = W64 4) = false by simpa using hK]
      try wp_auto
      wp_apply wp_mstep x c.st' g.st.st $$ [$Hcs] as %s' %o ⟨#Hs', %Ho⟩
      · ipureintro; exact Hb.1
      subst Ho
      wp_apply wp_outEqual y (mstepL x g.st.st).2
      cases hq : decide (y = (mstepL x g.st.st).2)
      · try wp_auto
        step_nil (by
          rw [stepL, ite_cond_eq_false _ _ (eq_false hE), hks,
            ite_cond_eq_false _ _ (eq_false (of_decide_eq_false hq))])
      · try wp_auto
        wp_apply wp_advance c g s' (mstepL x g.st.st).1 c.pend' g.pend $$ [$Hc $Hs' $Hcp] as %c' #Hc'
        · ipureintro; exact Hb.2.2
        wp_apply wp_slice_literal (l := [c'])
        isplitr
        · ipureintro; rfl
        iintro %lsl ⟨Hl1, _⟩
        wp_auto
        iapply HΦ
        rw [show stepL g x y = [⟨advanceL g.st (mstepL x g.st.st).1, g.pend⟩] by
          rw [stepL, ite_cond_eq_false _ _ (eq_false hE), hks,
            ite_cond_eq_true _ _ (eq_true (of_decide_eq_true hq))]]
        iframe
        iapply (BigSepL2.bigSepL2_singleton (PROP := IProp GF)).2
        iexact Hc'
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
      iexact Hc
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
      wp_apply wp_slice_literal (l := [(⟨c.st', o2, c.hist'⟩ : mcfg)])
      isplitr
      · ipureintro; rfl
      iintro %lsl2 ⟨Hl2, _⟩
      wp_auto
      iapply HΦ
      rw [show stepL g x y = [⟨g.st, x :: g.pend⟩] by rw [stepL, if_pos (Decidable.of_not_not hE)]; simp [hw]]
      iframe
      iapply (BigSepL2.bigSepL2_singleton (PROP := IProp GF)).2
      unfold cfgOwn
      isplit
      · iexact Hcs
      isplit
      · iexact Hch
      isplit
      · iexact Ho
      · ipureintro; exact Hhl

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
