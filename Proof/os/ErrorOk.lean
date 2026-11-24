/-
The errors of `os`'s models (`TrustedCode/os.lean`) are ones Go's `fmt` formats by their
`Error()` (`fmtErrorOk`, `Spec/fmt/ErrorOk.lean`): a `*PathError` whose fields are persistent and
whose `Err` is `fmtErrorOk` (its `Error()`, translated, concatenates `Op`, `Path` and
`Err.Error()`), and so `f.wrapErr(op, Errno(e))` for a nonzero `e` (`wp_wrapErrno_ok`).
-/
module

public import Proof.os.Base
public import Proof.syscall.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace os

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.fs.Assumptions]

/-- A `*PathError` at `pe` with persistent fields `op`, `path` and an `Err` that is `fmtErrorOk`
is `fmtErrorOk`. -/
theorem pathError_fmtErrorOk (pe : Loc) (op path : GoString) (err : GoInterface) :
    structFieldRef io.fs.PathError go!"Op" pe ↦□ op -∗
    structFieldRef io.fs.PathError go!"Path" pe ↦□ path -∗
    structFieldRef io.fs.PathError go!"Err" pe ↦□ err -∗
    EtcdGrove.fmtErrorOk (GF := GF) err -∗
    EtcdGrove.fmtErrorOk (GF := GF)
      (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe) := by
  cases err with
  | nil =>
    simp only [EtcdGrove.fmtErrorOk]
    iintro - - - %hf
    exact hf.elim
  | ok ii =>
  simp only [EtcdGrove.fmtErrorOk, _root_.Perennial.fmt.stringMethodSpec]
  iintro #Hop #Hpath #Herr ⟨%hms, #Hs⟩
  isplitr
  · ipureintro
    have h1 := (go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType io.fs.PathError.ty) go!"Format")
    have h2 := (go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType io.fs.PathError.ty) go!"Error")
    simp only [go.methodSetLookup] at h1 h2
    exact ⟨by simpa using h1, by simpa [EtcdGrove.noArgStringSig] using h2⟩
  imodintro
  iintro %Φ HΦ
  simp only [method_unfold]
  unfold io.fs.PathError.Error.impl
  wp_auto
  wp_bind (App (Val #(methods ii.ty go!"Error" ii.v)) (Val #()))
  iapply Hs
  inext
  iintro %s
  wp_auto
  iapply HΦ

/-- `pathError_fmtErrorOk` with the message bound: `op + " " + path + ": " + err.Error()`. -/
theorem pathError_fmtErrorOkLe (pe : Loc) (op path : GoString) (err : GoInterface) (B : Nat) :
    structFieldRef io.fs.PathError go!"Op" pe ↦□ op -∗
    structFieldRef io.fs.PathError go!"Path" pe ↦□ path -∗
    structFieldRef io.fs.PathError go!"Err" pe ↦□ err -∗
    EtcdGrove.fmtErrorOkLe (GF := GF) B err -∗
    EtcdGrove.fmtErrorOkLe (GF := GF) (op.length + path.length + 3 + B)
      (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe) := by
  cases err with
  | nil =>
    simp only [EtcdGrove.fmtErrorOkLe]
    iintro - - - %hf
    exact hf.elim
  | ok ii =>
  simp only [EtcdGrove.fmtErrorOkLe, EtcdGrove.stringMethodSpecLe]
  iintro #Hop #Hpath #Herr ⟨%hms, #Hs⟩
  isplitr
  · ipureintro
    have h1 := (go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType io.fs.PathError.ty) go!"Format")
    have h2 := (go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType io.fs.PathError.ty) go!"Error")
    simp only [go.methodSetLookup] at h1 h2
    exact ⟨by simpa using h1, by simpa [EtcdGrove.noArgStringSig] using h2⟩
  imodintro
  iintro %Φ HΦ
  simp only [method_unfold]
  unfold io.fs.PathError.Error.impl
  wp_auto
  wp_bind (App (Val #(methods ii.ty go!"Error" ii.v)) (Val #()))
  iapply Hs
  inext
  iintro %s %hs
  wp_auto
  iapply HΦ
  ipureintro
  simp only [List.length_append]
  have : (go!" " : GoString).length = 1 := rfl
  have : (go!": " : GoString).length = 2 := rfl
  omega

end wps

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : os.Assumptions]

/-- `f.wrapErr(op, Errno(e))` (`model.wrapErrno`) for a nonzero errno `e`: a fresh `*PathError`
as an `error`, one `fmt` formats (`fmtErrorOk`). `wp_wrapErrno` with the error's fact. -/
theorem wp_wrapErrno_ok (op : GoString) (inner : Loc) (name : GoString) (e : w64) (he : e ≠ 0)
    (Φ : val → IProp GF) :
    structFieldRef os.file go!"name" inner ↦□ name -∗ syscall.errnoOk (GF := GF) -∗
      (∀ pe : Loc, EtcdGrove.fmtErrorOk (GF := GF)
          (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe) -∗
        Φ #(interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)) -∗
      WP (App (App (App (Val os.model.wrapErrno) (Val #op)) (Val #inner)) (Val #e)) {{ Φ }} := by
  iintro #Hn #Hsys HΦ
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
  iapply (pathError_fmtErrorOk pe_ptr op name (errnoErr e)) $$ Op Path Err
  iapply (errnoErr_fmtErrorOk e he) $$ Hsys

/-- `wp_wrapErrno_ok` with the message bound: `op + " " + name + ": " + Errno(e).Error()`. -/
theorem wp_wrapErrno_okLe (op : GoString) (inner : Loc) (name : GoString) (e : w64) (he : e ≠ 0)
    (Φ : val → IProp GF) :
    structFieldRef os.file go!"name" inner ↦□ name -∗ syscall.errnoOk (GF := GF) -∗
      (∀ pe : Loc, EtcdGrove.fmtErrorOkLe (GF := GF)
          (op.length + name.length + 3 + syscall.errnoMsgMax)
          (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe) -∗
        Φ #(interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)) -∗
      WP (App (App (App (Val os.model.wrapErrno) (Val #op)) (Val #inner)) (Val #e)) {{ Φ }} := by
  iintro #Hn #Hsys HΦ
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
  iapply (pathError_fmtErrorOkLe pe_ptr op name (errnoErr e)) $$ Op Path Err
  iapply (errnoErr_fmtErrorOkLe e he) $$ Hsys

/-- A `*LinkError` at `le` with persistent fields `op`, `old`, `new` and an `Err` that is
`fmtErrorOk` is `fmtErrorOk` (its `Error()`, translated, concatenates the four). -/
theorem linkError_fmtErrorOk (le : Loc) (op old new : GoString) (err : GoInterface) :
    structFieldRef os.LinkError go!"Op" le ↦□ op -∗
    structFieldRef os.LinkError go!"Old" le ↦□ old -∗
    structFieldRef os.LinkError go!"New" le ↦□ new -∗
    structFieldRef os.LinkError go!"Err" le ↦□ err -∗
    EtcdGrove.fmtErrorOk (GF := GF) err -∗
    EtcdGrove.fmtErrorOk (GF := GF)
      (interface.mkOk (go.GoType.PointerType os.LinkError.ty) #le) := by
  cases err with
  | nil =>
    simp only [EtcdGrove.fmtErrorOk]
    iintro - - - - %hf
    exact hf.elim
  | ok ii =>
  simp only [EtcdGrove.fmtErrorOk, _root_.Perennial.fmt.stringMethodSpec]
  iintro #Hop #Hold #Hnew #Herr ⟨%hms, #Hs⟩
  isplitr
  · ipureintro
    have h1 := (go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType os.LinkError.ty) go!"Format")
    have h2 := (go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType os.LinkError.ty) go!"Error")
    simp only [go.methodSetLookup] at h1 h2
    exact ⟨by simpa using h1, by simpa [EtcdGrove.noArgStringSig] using h2⟩
  imodintro
  iintro %Φ HΦ
  simp only [method_unfold]
  unfold os.LinkError.Error.impl
  wp_auto
  wp_bind (App (Val #(methods ii.ty go!"Error" ii.v)) (Val #()))
  iapply Hs
  inext
  iintro %s
  wp_auto
  iapply HΦ

/-- `&PathError{op, path, Errno(e)}` (`model.pathError`) for a nonzero errno `e`: an `error`
`fmt` formats (`fmtErrorOk`). -/
theorem wp_pathError_ok (op path : GoString) (e : w64) (he : e ≠ 0) (Φ : val → IProp GF) :
    syscall.errnoOk (GF := GF) -∗ (∀ pe : Loc, EtcdGrove.fmtErrorOk (GF := GF)
        (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe) -∗
      Φ #(interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)) -∗
      WP (App (App (App (Val os.model.pathError) (Val #op)) (Val #path))
        (App (Val syscall.model.errno) (Val #e))) {{ Φ }} := by
  iintro #Hsys HΦ
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
  iapply (pathError_fmtErrorOk pe_ptr op path (errnoErr e)) $$ Op Path Err
  iapply (errnoErr_fmtErrorOk e he) $$ Hsys

/-- `&LinkError{op, old, new, Errno(e)}` (`model.linkError`) for a nonzero errno `e`: an `error`
`fmt` formats (`fmtErrorOk`). -/
theorem wp_linkError_ok (op old new : GoString) (e : w64) (he : e ≠ 0) (Φ : val → IProp GF) :
    syscall.errnoOk (GF := GF) -∗ (∀ le : Loc, EtcdGrove.fmtErrorOk (GF := GF)
        (interface.mkOk (go.GoType.PointerType os.LinkError.ty) #le) -∗
      Φ #(interface.mkOk (go.GoType.PointerType os.LinkError.ty) #le)) -∗
      WP (App (App (App (App (Val os.model.linkError) (Val #op)) (Val #old)) (Val #new))
        (App (Val syscall.model.errno) (Val #e))) {{ Φ }} := by
  iintro #Hsys HΦ
  wp_apply wp_errno
  unfold os.model.linkError
  rw [show os.model.LinkError = os.LinkError.ty by unfold os.LinkError.ty; rfl]
  iapply wp_fupd
  wp_auto
  iStructNamed le
  ipersist Op
  ipersist Old
  ipersist New
  ipersist Err
  imodintro
  iapply HΦ
  iapply (linkError_fmtErrorOk le_ptr op old new (errnoErr e)) $$ Op Old New Err
  iapply (errnoErr_fmtErrorOk e he) $$ Hsys

end wrap

end os

end Perennial
