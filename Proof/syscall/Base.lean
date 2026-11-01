/-
Shared definitions of the specs of `syscall`'s trusted models (`TrustedCode/syscall.lean`), used
by `os`'s and `golang.org/x/sys/unix`'s too: the errors they return (`errnoErr`). The models call
the Linux file extension (`GooseLang/Ext/OsFs`), whose resources the specs use.
-/
module

public import GeneratedProof.syscall
public import Proof.OsFsPrelude
public import GooseLang.Ext.OsFs.Write

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- `errnoErr(e)`: `nil` for 0, else the `Errno` `e` as an `error`. -/
def errnoErr [GooseExts] [GoGlobalContext] (e : w64) : GoInterface :=
  if e = 0 then interface.nil else interface.mkOk syscall.Errno.ty #e

theorem errno_ty_eq [GooseExts] [GoGlobalContext] :
    go.GoType.Named go!"syscall.Errno" [] = syscall.Errno.ty := by
  unfold syscall.Errno.ty; rfl

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

end wps

end Perennial
