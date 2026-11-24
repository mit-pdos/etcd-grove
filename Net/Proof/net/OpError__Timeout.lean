/-
The proof of `Net/Spec/net/OpError__Timeout.lean`: `OpError.Timeout.impl`'s type assertions on
`Err` (`model.errFlag`), else the extension's `AnyBool`.
-/
module

public import Net.Spec.net.OpError__Timeout
public import Net.Proof.net.Errors

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]
variable [go.BasicIntoValInj]

theorem errNetClosing_ty_ne_ptr (t : go.GoType) :
    internal.poll.errNetClosing.ty ≠ go.GoType.PointerType t := by
  unfold internal.poll.errNetClosing.ty; intro h; cases h

theorem deadline_ty_ne_timeout :
    go.GoType.PointerType internal.poll.DeadlineExceededError.ty ≠
      go.GoType.PointerType timeoutError.ty := by
  unfold internal.poll.DeadlineExceededError.ty timeoutError.ty; intro h; cases h

theorem OpError.Timeout.wp_proof : OpError.Timeout.spec (GF := GF) (hG := hG) := by
  intro pe v
  wp_start as ⟨#Hpe, #Hok⟩
  ihave #H2 := Hpe
  iStructNamed H2
  unfold opErrOk netOwnErr
  icases Hok with ⟨#He, -, -⟩
  (try wp_method_call)
  wp_auto
  icases He with (%he | ⟨%p, %he⟩ | ⟨%p, %he⟩ | #He)
  · rw [he]; unfold closedErr
    wp_auto
    rw [show go.typeSetContains internal.poll.errNetClosing.ty timeout.ty = true by go_type_set]
    wp_auto
    wp_method_call
    wp_auto
    iapply HΦ
    ipureintro
    unfold ErrFlag interface.mkOk; dsimp only
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> first | rfl | (simp only [goose_wp_simp_extra] at h)
  · rw [he]
    wp_auto
    rw [show go.typeSetContains (go.GoType.PointerType internal.poll.DeadlineExceededError.ty)
      timeout.ty = true by go_type_set]
    wp_auto
    wp_method_call
    wp_auto
    iapply HΦ
    ipureintro
    unfold ErrFlag interface.mkOk; dsimp only
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> first | rfl | (simp only [goose_wp_simp_extra] at h)
  · rw [he]
    wp_auto
    rw [show go.typeSetContains (go.GoType.PointerType timeoutError.ty) timeout.ty = true by
      go_type_set]
    wp_auto
    wp_method_call
    wp_auto
    iapply HΦ
    ipureintro
    unfold ErrFlag interface.mkOk; dsimp only
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;> first | rfl | (simp only [goose_wp_simp_extra] at h)
  · unfold sysErr
    icases He with ⟨%p, %name, %n, %h, #Hp⟩
    obtain ⟨he, -, hn⟩ := h
    rw [he]
    iStructNamed Hp
    wp_auto
    rw [show go.typeSetContains syscall.Errno.ty timeout.ty = true by go_type_set]
    wp_auto
    wp_method_call
    wp_auto
    simp only [syscall.EWOULDBLOCK, syscall.ETIMEDOUT]
    repeat' (first | wp_if_destruct | wp_auto)
    all_goals
      iapply HΦ
      ipureintro
      unfold ErrFlag interface.mkOk; dsimp only
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp only [goose_wp_simp_extra] at h

end proof

end net
end Perennial
