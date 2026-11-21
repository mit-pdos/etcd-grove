/-
Proof of `apierrors.IsTooManyRequests` (`Spec/k8s_io/apimachinery/pkg/api/errors/IsTooManyRequests.lean`) over its body
(prove-k8s2, 2026-11-20; until then a trust-boundary axiom).
-/
module

public import Spec.k8s_io.apimachinery.pkg.api.errors.IsTooManyRequests
public import Spec.k8s_io.apimachinery.pkg.api.errors.reasonAndCodeForError
public import Proof.k8s_io.apimachinery.pkg.api.errors.Checks

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

theorem IsTooManyRequests.wp_proof
    (wp_reasonAndCodeForError : reasonAndCodeForError.spec (GF := GF) (hG := hG)) :
    IsTooManyRequests.spec (GF := GF) (hG := hG) := by
  intro err
  wp_start as #Hok
  ihave #Hok2 : apiErrOk (GF := GF) err $$ []
  · icases Hok with (%h | #H)
    · subst h
      unfold apiErrOk apiErrAt plainLeaf
      iright; ileft; ipureintro; exact Or.inl rfl
    · iexact H
  wp_auto
  wp_apply (wp_reasonAndCodeForError err) $$ [Hok2] as %r %c #Hrc
  · iframe
    iexact Hok2
  try wp_auto
  by_cases hr : r = go!"TooManyRequests" <;> by_cases hc : c = W32 429 <;>
    simp only [hr, _root_.decide_true, _root_.decide_false] <;>
    (try wp_auto) <;>
    (try simp only [hc, _root_.decide_true, _root_.decide_false]) <;>
    (try wp_auto) <;>
  · iapply HΦ
    iintro !> %w #Hw
    ihave %h := Hrc $$ Hw
    ipureintro
    cases w <;> obtain ⟨h1, h2⟩ := h <;> simp_all (config := {decide := true})

end proof

end apierrors
end EtcdGrove
end Perennial
