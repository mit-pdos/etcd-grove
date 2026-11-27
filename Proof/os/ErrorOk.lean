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

/-- `modelErrno(e)` (syscall's `errnoErr` of an errno): `errnoErr e`. -/
theorem wp_modelErrno (e : w64) (Φ : val → IProp GF) :
    Φ #(errnoErr e) ⊢ WP (App (Val (@! os.modelErrno)) (Val #e)) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  try wp_auto
  by_cases he : e = 0
  · subst he
    try wp_auto
    unfold errnoErr; rw [if_pos rfl]; iexact HΦ
  · simp only [show decide (e = W64 0) = false from decide_eq_false he]
    try wp_auto
    unfold errnoErr; rw [if_neg he]; iexact HΦ

/-- `modelPathError(op, path, err)`: a fresh `*PathError` as an `error`. -/
theorem wp_modelPathError (op path : GoString) (err : GoInterface) (Φ : val → IProp GF) :
    (∀ pe : Loc, Φ #(interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)) ⊢
      WP (App (App (App (Val (@! os.modelPathError)) (Val #op)) (Val #path))
        (Val #err)) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  try wp_auto
  wp_alloc pe as Hpe
  try wp_auto
  iapply HΦ

/-- `modelPathError(op, path, Errno(e))` for a nonzero errno `e`: a fresh `*PathError` as an
`error`, one `fmt` formats (`fmtErrorOk`). -/
theorem wp_modelPathError_ok (op path : GoString) (e : w64) (he : e ≠ 0) (Φ : val → IProp GF) :
    syscall.errnoOk (GF := GF) -∗ (∀ pe : Loc, EtcdGrove.fmtErrorOk (GF := GF)
        (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe) -∗
      Φ #(interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)) -∗
      WP (App (App (App (Val (@! os.modelPathError)) (Val #op)) (Val #path))
        (Val #(errnoErr e))) {{ Φ }} := by
  iintro #Hsys HΦ
  wp_func_call; wp_call
  iapply wp_fupd
  try wp_auto
  wp_alloc pe as Hpe
  iStructNamed Hpe
  ipersist Op
  ipersist Path
  ipersist Err
  try wp_auto
  imodintro
  iapply HΦ
  iapply (pathError_fmtErrorOk pe op path (errnoErr e)) $$ Op Path Err
  iapply (errnoErr_fmtErrorOk e he) $$ Hsys

/-- `wp_modelPathError_ok` with the message bound: `op + " " + path + ": " + Errno(e).Error()`. -/
theorem wp_modelPathError_okLe (op path : GoString) (e : w64) (he : e ≠ 0) (Φ : val → IProp GF) :
    syscall.errnoOk (GF := GF) -∗ (∀ pe : Loc, EtcdGrove.fmtErrorOkLe (GF := GF)
        (op.length + path.length + 3 + syscall.errnoMsgMax)
        (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe) -∗
      Φ #(interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)) -∗
      WP (App (App (App (Val (@! os.modelPathError)) (Val #op)) (Val #path))
        (Val #(errnoErr e))) {{ Φ }} := by
  iintro #Hsys HΦ
  wp_func_call; wp_call
  iapply wp_fupd
  try wp_auto
  wp_alloc pe as Hpe
  iStructNamed Hpe
  ipersist Op
  ipersist Path
  ipersist Err
  try wp_auto
  imodintro
  iapply HΦ
  iapply (pathError_fmtErrorOkLe pe op path (errnoErr e) syscall.errnoMsgMax) $$ Op Path Err
  iapply (errnoErr_fmtErrorOkLe e he) $$ Hsys

/-- `modelPathError(op, path, modelErrno(e))` as one GooseLang expression (the shape of a hand-written
GooseLang model calling the two, `TrustedCode/go_etcd_io/etcd/pkg/v3/runtime.lean`), `e ≠ 0`. -/
theorem wp_pathError_ok (op path : GoString) (e : w64) (he : e ≠ 0) (Φ : val → IProp GF) :
    syscall.errnoOk (GF := GF) -∗ (∀ pe : Loc, EtcdGrove.fmtErrorOk (GF := GF)
        (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe) -∗
      Φ #(interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)) -∗
      WP (App (App (App (Val (@! os.modelPathError)) (Val #op)) (Val #path))
        (App (Val (@! os.modelErrno)) (Val #e))) {{ Φ }} := by
  iintro #Hsys HΦ
  wp_apply wp_modelErrno
  wp_apply wp_modelPathError_ok op path e he $$ Hsys
  iexact HΦ

/-- `modelWrapErrno(op, inner, e)` (`f.wrapErr(op, Errno(e))`) for a nonzero errno `e`: a fresh
`*PathError` as an `error`, one `fmt` formats (`fmtErrorOk`). -/
theorem wp_wrapErrno_ok (op : GoString) (inner : Loc) (name : GoString) (e : w64) (he : e ≠ 0)
    (Φ : val → IProp GF) :
    structFieldRef os.file go!"name" inner ↦□ name -∗ syscall.errnoOk (GF := GF) -∗
      (∀ pe : Loc, EtcdGrove.fmtErrorOk (GF := GF)
          (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe) -∗
        Φ #(interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)) -∗
      WP (App (App (App (Val (@! os.modelWrapErrno)) (Val #op)) (Val #inner)) (Val #e)) {{ Φ }} := by
  iintro #Hn #Hsys HΦ
  wp_func_call; wp_call
  try wp_auto
  wp_apply wp_modelErrno
  try wp_auto
  wp_apply wp_modelPathError_ok op name e he $$ Hsys
  iintro %pe #Hok
  try wp_auto
  iapply HΦ $$ Hok

/-- `wp_wrapErrno_ok` with the message bound: `op + " " + name + ": " + Errno(e).Error()`. -/
theorem wp_wrapErrno_okLe (op : GoString) (inner : Loc) (name : GoString) (e : w64) (he : e ≠ 0)
    (Φ : val → IProp GF) :
    structFieldRef os.file go!"name" inner ↦□ name -∗ syscall.errnoOk (GF := GF) -∗
      (∀ pe : Loc, EtcdGrove.fmtErrorOkLe (GF := GF)
          (op.length + name.length + 3 + syscall.errnoMsgMax)
          (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe) -∗
        Φ #(interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)) -∗
      WP (App (App (App (Val (@! os.modelWrapErrno)) (Val #op)) (Val #inner)) (Val #e)) {{ Φ }} := by
  iintro #Hn #Hsys HΦ
  wp_func_call; wp_call
  try wp_auto
  wp_apply wp_modelErrno
  try wp_auto
  wp_apply wp_modelPathError_okLe op name e he $$ Hsys
  iintro %pe #Hok
  try wp_auto
  iapply HΦ $$ Hok

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

end wrap

end os

end Perennial
