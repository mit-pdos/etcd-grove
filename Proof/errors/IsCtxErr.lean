/-
`errors.Is` of a context's error against `context.Canceled` or `context.DeadlineExceeded`, proved
over Perennial's `errors.Is` at comparable targets (perennial#677; a trust-boundary axiom until
errors-is-axioms, 2026-11-22). Both `err` and `target` are context errors (`context.isCtxErr`,
`target`'s from `isPkgInit context`): `Canceled`'s `*errorString` or `DeadlineExceeded`'s
`deadlineExceededError{}`. Each is a leaf error without an `Is` method (one-error tree with exact
relations, `errorWalkTree_leaf`), and its type is comparable: a pointer (`comparableTarget_pointer`)
or a field-less struct, whose `==` is `true` (`deadlineExceededError_comparable`). So Go's `Is`
answers `true` when `err == target` (`isWalk_eq_true`).
-/
module

public import Spec.errors.IsCtxErr
public import Proof.errors.CtxErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

theorem errors.IsCtxErr.wp_proof
    (wp_Is : _root_.Perennial.errors.Is.spec (GF := GF) (hG := hG)) :
    errors.IsCtxErr.spec (GF := GF) (hG := hG) := by
  intro err target
  iintro %Φ ⟨#Hinit, #Hctx, #He, #Ht⟩ HΦ
  ihave #Htc : (context.isCtxErr target : IProp GF) $$ []
  · icases Ht with (Ht | Ht)
    · iapply context.isCtxErr_of_Canceled $$ Hctx Ht
    · iapply context.isCtxErr_of_DeadlineExceeded $$ Hctx Ht
  ihave %Hes := isCtxErr_shape err $$ He
  ihave %Hts := isCtxErr_shape target $$ Htc
  obtain ⟨ii, rfl, hleaf, hIs, hshape⟩ := Hes
  obtain ⟨tii, rfl, -, -, htshape⟩ := Hts
  ihave #Htree := _root_.Perennial.errors.errorWalkTree_leaf (GF := GF) ii (GoInterface.ok tii)
    hleaf hIs
  have hcmp : _root_.Perennial.errors.ComparableTarget (· = GoInterface.ok ii)
      (GoInterface.ok tii) := by
    intro tii' ht
    cases ht
    rcases htshape with hp | rfl
    · apply _root_.Perennial.errors.comparableErr_pointer _ _ hp
      intro jj tjj hS ht hty
      cases hS; cases ht
      rcases hshape with ⟨T, l, hT, hl⟩ | rfl
      · exact ⟨l, hl⟩
      · obtain ⟨T', l', hT', -⟩ := hp
        exfalso
        simp only at hty
        rw [hT'] at hty
        unfold _root_.Perennial.context.deadlineExceededError.ty at hty
        cases hty
    · apply deadlineExceededError_comparable
      intro jj hS hty
      cases hS
      rcases hshape with ⟨T, l, hT, -⟩ | rfl
      · exfalso
        rw [hT] at hty
        unfold _root_.Perennial.context.deadlineExceededError.ty at hty
        cases hty
      · rfl
  wp_apply +noauto wp_Is (· = GoInterface.ok ii) _ _ (GoInterface.ok ii) (GoInterface.ok tii) hcmp
    $$ [$Hinit $Htree] as %b ⟨-, %Hw⟩
  · ipureintro; rfl
  iapply HΦ
  ipureintro
  intro heq
  exact _root_.Perennial.errors.isWalk_eq_true rfl heq (Hw (by simp) (by simp))

end proof

end EtcdGrove
end Perennial
