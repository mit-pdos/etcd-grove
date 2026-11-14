/-
`err` is a `*PathError` of the errno `e` (`os.errnoPathErr`): what `os`'s models return on a failed
system call (`model.pathError`, `model.wrapErrno`), with the lemmas producing it and formatting it.
Moved out of `NsChildS.lean` (2026-11-14) so that `NsS.lean`'s directory specs state their errors.
Lean-first.
-/
module

public import LinuxFs.Proof.os.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

namespace os

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `err` is a `*PathError` whose `Err` is the errno `e` (`errnoErr e`), its fields persistent: what
`os`'s models return on a failed system call (`model.pathError`, `model.wrapErrno`). -/
def errnoPathErr (err : GoInterface) (e : w64) : IProp GF :=
  iprop(∃ (pe : Loc) (op path : GoString),
    ⌜err = interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe⌝ ∗
    structFieldRef io.fs.PathError go!"Op" pe ↦□ op ∗
    structFieldRef io.fs.PathError go!"Path" pe ↦□ path ∗
    structFieldRef io.fs.PathError go!"Err" pe ↦□ errnoErr e)

instance errnoPathErr_persistent (err : GoInterface) (e : w64) :
    Persistent (errnoPathErr (GF := GF) err e) := by
  unfold errnoPathErr; infer_instance

theorem errnoPathErr_ne (err : GoInterface) (e : w64) :
    errnoPathErr (GF := GF) err e ⊢ ⌜err ≠ interface.nil⌝ := by
  unfold errnoPathErr
  iintro ⟨%pe, %op, %path, %h, -⟩
  ipureintro; subst h; intro h; cases h

end defs

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : os.Assumptions]

/-- A `*PathError` of a nonzero errno is one `fmt` formats. -/
theorem errnoPathErr_fmtErrorOk (err : GoInterface) (e : w64) (he : e ≠ 0) :
    errnoPathErr (GF := GF) err e ⊢ EtcdGrove.fmtErrorOk (GF := GF) err := by
  unfold errnoPathErr
  iintro ⟨%pe, %op, %path, %h, #Op, #Path, #Err⟩
  subst h
  iapply (pathError_fmtErrorOk pe op path (errnoErr e)) $$ Op Path Err
  iapply (errnoErr_fmtErrorOk e he)

theorem errnoPathErr_fmtErrorOkOrNil (err : GoInterface) (e : w64) (he : e ≠ 0) :
    errnoPathErr (GF := GF) err e ⊢ EtcdGrove.fmtErrorOkOrNil (GF := GF) err := by
  iintro #H
  iapply (EtcdGrove.fmtErrorOkOrNil_of _)
  iapply (errnoPathErr_fmtErrorOk err e he) $$ H

/-- `&PathError{op, path, Errno(e)}` (`model.pathError`): `errnoPathErr`. -/
theorem wp_pathError_errno (op path : GoString) (e : w64) (Φ : val → IProp GF) :
    (∀ err : GoInterface, errnoPathErr (GF := GF) err e -∗ Φ #err) ⊢
      WP (App (App (App (Val os.model.pathError) (Val #op)) (Val #path))
        (App (Val syscall.model.errno) (Val #e))) {{ Φ }} := by
  iintro HΦ
  wp_apply wp_errno
  unfold os.model.pathError
  iapply wp_fupd
  wp_auto
  iStructNamed pe
  ipersist Op
  ipersist Path
  ipersist Err
  imodintro
  iapply HΦ
  unfold errnoPathErr
  iexists pe_ptr, op, path
  isplitr
  · ipureintro; rfl
  iframe Op Path Err

/-- `f.wrapErr(op, Errno(e))` (`model.wrapErrno`): `errnoPathErr`. -/
theorem wp_wrapErrno_errno (op : GoString) (inner : Loc) (name : GoString) (e : w64)
    (Φ : val → IProp GF) :
    structFieldRef os.file go!"name" inner ↦□ name -∗
      (∀ err : GoInterface, errnoPathErr (GF := GF) err e -∗ Φ #err) -∗
      WP (App (App (App (Val os.model.wrapErrno) (Val #op)) (Val #inner)) (Val #e)) {{ Φ }} := by
  iintro #Hn HΦ
  unfold os.model.wrapErrno os.model.pathError
  rw [file_ty_eq]
  wp_auto
  iapply wp_fupd
  wp_apply wp_errno
  iStructNamed pe
  ipersist Op
  ipersist Path
  ipersist Err
  imodintro
  iapply HΦ
  unfold errnoPathErr
  iexists pe_ptr, op, name
  isplitr
  · ipureintro; rfl
  iframe Op Path Err

end wps

end os

end Perennial

end
