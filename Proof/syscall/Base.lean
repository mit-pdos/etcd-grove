/-
Shared definitions of the specs of `syscall`'s trusted models (`TrustedCode/syscall.lean`), used
by `os`'s and `golang.org/x/sys/unix`'s too: the errors they return (`errnoErr`). The models call
the Linux file extension (`GooseLang/Ext/Fs`), whose resources the specs use.
-/
module

public import GeneratedProof.syscall
public import Proof.FsPrelude
public import GooseLang.Ext.Fs.Write

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- `errnoErr(e)`: `nil` for 0, else the `Errno` `e` as an `error`. -/
def errnoErr [GooseExts] [GoGlobalContext] (e : w64) : GoInterface :=
  if e = 0 then interface.nil else interface.mkOk syscall.Errno.ty #e

theorem errno_ty_eq [GooseExts] [GoGlobalContext] :
    go.GoType.Named go!"syscall.Errno" [] = syscall.Errno.ty := by
  unfold syscall.Errno.ty; rfl

/-- One call of a primitive stub of a Go model (`models/<pkg>/stubs.go`, its GooseLang model `X.impl`
in `TrustedCode/`): resolve it, unfold its model, and take the call's step; what is left is the
extension's operation. -/
macro "wp_stub " i:ident : tactic => `(tactic| (wp_func_call; unfold $i:ident; wp_call; try wp_pures))

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : syscall.Assumptions]

/-- The models' `errnoErr`. -/
theorem wp_errno (e : w64) (Φ : val → IProp GF) :
    Φ #(errnoErr e) ⊢ WP (syscall.model.errno #e) {{ Φ }} := by
  iintro HΦ
  unfold syscall.model.errno
  wp_auto
  by_cases he : e = 0
  · subst he
    wp_auto
    unfold errnoErr; rw [if_pos rfl]; iexact HΦ
  · simp only [show decide (e = W64 0) = false from decide_eq_false he]
    rw [errno_ty_eq]
    wp_auto
    unfold errnoErr; rw [if_neg he]; iexact HΦ

/-- Go's `errnoErr` (the model's, `models/syscall/model.go`): `errnoErr e`. -/
theorem wp_errnoErr (e : w64) :
    {{ (True : IProp GF) }}
      (App (Val (@! syscall.errnoErr)) (Val #e))
    {{ RET #(errnoErr e); True }} := by
  wp_start as -
  try wp_auto
  by_cases he : e = 0
  · subst he
    wp_auto
    unfold errnoErr; rw [if_pos rfl]; iapply HΦ; itrivial
  · simp only [show decide (e = W64 0) = false from decide_eq_false he]
    wp_auto
    unfold errnoErr; rw [if_neg he]; iapply HΦ; itrivial

end wps

end Perennial
