/-
Lean-first (no Rocq counterpart).

The proof of `Model`: the three closures meet `initSpec`, `stepSpec` and `equalSpec` of
`regS`; the other fields are `nil`. `Step`'s `state.(string)`, `input.(Op)` and
`output.(string)` go through by `rep` and `ioOk` (a boxed `string`, `Op` and `string`); a write
returns `true` and its value (`regStep_put`), a read compares the output with the state
(`regStep_get`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Model

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace logkvcompact

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.logkvcompact.Assumptions]

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
    simp only [regS, regM]
    ipureintro; trivial
  isplitr
  · -- Step
    iright
    isplitr
    · ipureintro; exact ⟨trivial, nofun⟩
    unfold stepSpec
    iintro %k %v %s %i %o
    iintro !> %Φ' Hpre HΦ'
    simp only [regS]
    icases Hpre with ⟨-, %Hrep, %Hio⟩
    obtain ⟨b, w, rfl, Ho⟩ := Hio
    subst Hrep
    wp_auto
    cases b with
    | true =>
      wp_auto
      iapply HΦ'
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro
        simp only [regM, regStep_put, Option.isSome_some]
      unfold stepPost
      simp only [regM, regStep_put]
      ipureintro; trivial
    | false =>
      obtain ⟨x, rfl⟩ := Ho rfl
      wp_auto
      iapply HΦ'
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro
        simp only [regM, regStep_get]
        split <;> simp_all
      unfold stepPost
      simp only [regM, regStep_get]
      by_cases hx : x = s
      · simp only [hx, ite_true]; ipureintro; trivial
      · simp only [hx, ite_false]; itrivial
  isplitr
  · ipureintro; nofun
  isplitr
  · -- Equal
    unfold equalSpec
    iintro %k %j %v %w %s %t
    iintro !> %Φ' Hpre HΦ'
    simp only [regS]
    icases Hpre with ⟨%Hv, %Hw⟩
    subst Hv Hw
    wp_auto
    iapply HΦ'
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    ipureintro
    intro h
    exact of_decide_eq_true h
  ileft
  ipureintro; trivial

end proof

end logkvcompact
end lintest
end EtcdGrove
end Perennial
