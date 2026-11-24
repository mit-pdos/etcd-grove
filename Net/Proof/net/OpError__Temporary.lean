/-
The proof of `Net/Spec/net/OpError__Temporary.lean`, over Go's own `OpError.Temporary`: under
`opErrOk`, `Err` is one of net's own errors (`netOwnErr`), whose `Temporary` (and, for an
`*os.SyscallError`, its `Errno`'s `Temporary` and `Timeout`) is translated Go.
-/
module

public import Net.Spec.net.OpError__Temporary
public import Net.Proof.net.Errors
public import Net.Proof.net.OpError__Timeout

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

/-- `syscall.Errno(n).Timeout()`: some answer. -/
private theorem wp_Errno_Timeout (n : w64) (Φ : val → IProp GF) :
    (∀ b : Bool, Φ #b) -∗
    WP (App (Val #(methods syscall.Errno.ty go!"Timeout" #n)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_method_call
  wp_auto
  simp only [syscall.EWOULDBLOCK, syscall.ETIMEDOUT]
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals iapply HΦ

theorem OpError.Temporary.wp_proof : OpError.Temporary.spec (GF := GF) (hG := hG) := by
  intro pe v
  wp_start as ⟨#Hpe, #Hok⟩
  ihave #H2 := Hpe
  iStructNamed H2
  unfold opErrOk netOwnErr
  icases Hok with ⟨#He, -, -⟩
  (try wp_method_call)
  icases He with (%he | ⟨%p, %he⟩ | ⟨%p, %he⟩ | #He)
  · rw [he]; unfold closedErr
    repeat' (first | wp_if_destruct |
      (rw [show go.typeSetContains (internal.poll.errNetClosing.ty) temporary.ty = true by go_type_set]) |
      (rw [show go.typeSetContains (internal.poll.errNetClosing.ty) syscall.Errno.ty = false by go_type_set]) |
      wp_method_call | (wp_func_call; wp_call) | wp_auto)
    all_goals
      iapply HΦ
      ipureintro
      unfold ErrFlag interface.mkOk; dsimp only
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> first | rfl | (simp only [goose_wp_simp_extra] at h)
  · rw [he]
    repeat' (first | wp_if_destruct |
      (rw [show go.typeSetContains (go.GoType.PointerType internal.poll.DeadlineExceededError.ty) temporary.ty = true by go_type_set]) |
      (rw [show go.typeSetContains (go.GoType.PointerType internal.poll.DeadlineExceededError.ty) syscall.Errno.ty = false by go_type_set]) |
      wp_method_call | (wp_func_call; wp_call) | wp_auto)
    all_goals
      iapply HΦ
      ipureintro
      unfold ErrFlag interface.mkOk; dsimp only
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> first | rfl | (simp only [goose_wp_simp_extra] at h)
  · rw [he]
    repeat' (first | wp_if_destruct |
      (rw [show go.typeSetContains (go.GoType.PointerType timeoutError.ty) temporary.ty = true by go_type_set]) |
      (rw [show go.typeSetContains (go.GoType.PointerType timeoutError.ty) syscall.Errno.ty = false by go_type_set]) |
      wp_method_call | (wp_func_call; wp_call) | wp_auto)
    all_goals
      iapply HΦ
      ipureintro
      unfold ErrFlag interface.mkOk; dsimp only
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> first | rfl | (simp only [goose_wp_simp_extra] at h)
  · unfold sysErr
    icases He with ⟨%p, %name, %n, %he, #Hp⟩
    rw [he.1]
    ihave #Hp2 := Hp
    iStructNamed Hp2
    haveI : go.NotInterface go.uintptr := ⟨by simp [go.uintptr]⟩
    repeat' (first | wp_if_destruct |
      (rw [show go.typeSetContains syscall.Errno.ty temporary.ty = true by go_type_set]) |
      (rw [show go.typeSetContains (go.GoType.PointerType os.SyscallError.ty) temporary.ty = true by go_type_set]) |
      (rw [show go.typeSetContains (go.GoType.PointerType os.SyscallError.ty) syscall.Errno.ty = false by go_type_set]) |
      wp_method_call | (wp_func_call; wp_call) | wp_auto |
      (wp_apply wp_Errno_Timeout as %b))
    all_goals
      iapply HΦ
      ipureintro
      unfold ErrFlag interface.mkOk; dsimp only
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> first | rfl | (simp only [goose_wp_simp_extra] at h)

end proof

end net
end Perennial
