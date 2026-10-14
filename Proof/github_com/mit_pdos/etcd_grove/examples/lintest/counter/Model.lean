/-
Lean-first (no Rocq counterpart).

The proof of `Model`: the three closures meet `initSpec`, `stepSpec` and `equalSpec` of
`counterS`; the other fields are `nil`. `Step`'s `state.(int64)` and `output.(int64)` go through
by `rep` and `ioOk` (boxed `int64`s), and its verdict is `counterM.step`'s: the output is
compared with the next state `counterNext s input` (`input != nil`), which `Step` returns.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Model

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace counter

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.counter.Assumptions]

theorem Model.wp_proof : Model.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_func_lits
  wp_auto
  iapply HΦ
  unfold isModel isEqHash
  simp only
  isplitr
  · ipureintro; trivial
  isplitr
  · -- Init
    unfold initSpec
    iintro !> %Φ' _ HΦ'
    wp_auto
    iapply HΦ'
    simp only [counterS, counterM]
    ipureintro; trivial
  isplitr
  · -- Step
    iright
    isplitr
    · ipureintro; exact ⟨trivial, nofun⟩
    unfold stepSpec
    iintro %v %s %i %o
    iintro !> %Φ' Hpre HΦ'
    simp only [counterS]
    icases Hpre with ⟨%Hrep, %Hio⟩
    obtain ⟨x, rfl⟩ := Hio
    subst Hrep
    wp_auto
    cases i with
    | nil =>
      wp_auto
      iapply HΦ'
      isplitr
      · ipureintro
        rw [counterM_step_box]
        by_cases h : x = s <;> simp [h, counterNext, isInc]
      have H := stepPost_counter (GF := GF) s x GoInterface.nil
      simp only [counterS, counterNext, isInc, ite_false, Bool.false_eq_true] at H
      iapply H
    | ok ii =>
      wp_auto
      iapply HΦ'
      isplitr
      · ipureintro
        rw [counterM_step_box]
        simp only [counterNext, isInc, ite_true]
        split <;> simp_all
      have H := stepPost_counter (GF := GF) s x (GoInterface.ok ii)
      simp only [counterS, counterNext, isInc, ite_true] at H
      iapply H
  isplitr
  · ipureintro; nofun
  isplitr
  · -- Equal
    unfold equalSpec
    iintro %v %w %s %t
    iintro !> %Φ' Hpre HΦ'
    simp only [counterS]
    icases Hpre with ⟨%Hv, %Hw⟩
    subst Hv Hw
    wp_auto
    iapply HΦ'
    ipureintro
    intro h
    exact of_decide_eq_true h
  ileft
  ipureintro; trivial

end proof

end counter
end lintest
end EtcdGrove
end Perennial
