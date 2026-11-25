/-
`errors.Is` at the target `context.DeadlineExceeded`, proved over Perennial's `errors.Is` at
comparable targets (perennial#677). It was a trust-boundary axiom until errors-is-deadline
(2026-11-23). `isPkgInit context` makes the target `deadlineExceededError{}`
(`deadlineExceeded_value`). Its type is a field-less struct, comparable with the tree's errors of its
type, which hold `deadlineExceededError{}` (`deTyped`, `deadlineExceededError_comparable`). Go's walk
answers `true` only at an error of the tree that is the target or whose `Is` said so
(`errors.isWalkL_true_mem`, as `errors.wp_Is_tree`).
-/
module

public import Spec.errors.IsDeadlineExceeded
public import Perennial.Spec.errors.Is

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

theorem errors.IsDeadlineExceeded.wp_proof
    (wp_Is : _root_.Perennial.errors.Is.spec (GF := GF) (hG := hG)) :
    errors.IsDeadlineExceeded.spec (GF := GF) (hG := hG) := by
  intro S M err target
  iintro %Φ ⟨#Hinit, #Hctx, #Ht, #Htree, %HS, %Hdt⟩ HΦ
  ihave %Htv := deadlineExceeded_value target $$ Hctx Ht
  subst Htv
  have hcmp : _root_.Perennial.errors.ComparableTarget (GF := GF) S
      (interface.mkOk _root_.Perennial.context.deadlineExceededError.ty
        #(zero_val _root_.Perennial.context.deadlineExceededError)) := by
    intro tii ht
    cases ht
    exact deadlineExceededError_comparable S (fun ii hS hty => Hdt ii hS hty)
  wp_apply +noauto wp_Is S (_root_.Perennial.errors.isRelOf M)
    (_root_.Perennial.errors.unwrapRelOf S) err _ hcmp $$ [$Hinit $Htree] as %b ⟨%Hnil, %Hw⟩
  · ipureintro; exact HS
  iapply HΦ
  ipureintro
  intro hb
  subst hb
  by_cases hn : err = interface.nil
  · subst hn
    have h := Hnil (Or.inl rfl)
    simp [interface.mkOk] at h
  · exact _root_.Perennial.errors.isWalkL_true_mem (Hw hn (by simp [interface.mkOk]))
      (fun e he => by rw [List.mem_singleton.mp he]; exact HS)

end proof

end EtcdGrove
end Perennial
