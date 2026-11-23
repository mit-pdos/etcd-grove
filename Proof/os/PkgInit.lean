/-
The package-initialization instances of `os` and `io/fs`, this repository's translations (project
bboltfs's, `Code/os.lean`, `Code/io/fs.lean`: names only but for the types and the functions the
Linux file extension fsExt models), which every project translates against since 2026-11-03
(`os=`, `io/fs=` in `etc/goose.py`; until then raft, the server and the k8s packages used
Perennial's names-only `os`, which bbolt's `os.FileMode` fields cannot use). Here so that raft
(its default logger loads `os.Stderr`), bbolt and minibolt share them: `IsPkgInit` must have one
instance per package (moved out of raft's `Base.lean`).
-/
module

public import GeneratedProof.os
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.errors
public import Perennial.Proof.io
public import Proof.syscall.PkgInit
public import Proof.internal.poll.PkgInit
public import Perennial.Proof.sync.Base
public import Perennial.Proof.time.Base
public import Perennial.Proof.internal.oserror.Base
public import Spec.fmt.ErrorOk

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace io.fs

/-- `io/fs`: its five error variables, which `os`'s initializer copies, hold some error for good
(2026-11-07: its variables' initializers are translated), `ErrExist` a non-nil one (internal/oserror's
`errors.New`; `wal.Create` returns `os.ErrExist` as its error, 2026-11-14), `ErrNotExist` an `*errorString`
(internal/oserror's `errors.New`, which it holds: `wal-vsnap4`; 2026-11-22), `ErrClosed` one `fmt`
formats (internal/oserror's `errors.New`; the closed-file `(*os.File).Close` wraps it, 2026-11-14). -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.io.fs :=
  define_is_pkg_init iprop(
    (∃ e : GoInterface, typedPointsto (globalAddr ErrInvalid) e DFrac.discard) ∗
    (∃ e : GoInterface, typedPointsto (globalAddr ErrPermission) e DFrac.discard) ∗
    (∃ e : GoInterface, ⌜e ≠ interface.nil⌝ ∗ typedPointsto (globalAddr ErrExist) e DFrac.discard) ∗
    (∃ x : Loc, typedPointsto (globalAddr ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard ∗
      typedPointsto (globalAddr _root_.Perennial.internal.oserror.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard) ∗
    (∃ e : GoInterface, EtcdGrove.fmtErrorOk e ∗ typedPointsto (globalAddr ErrClosed) e DFrac.discard))
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.io.fs :=
  build_get_is_pkg_init_wf

end io.fs

namespace os

/-- `os`: `Stderr` holds a fixed `*File`, which raft's initializer loads (`defaultLogger`); the
trusted model of its initializer (`TrustedCode/os.lean`) allocates it (2026-11-07; until then an
assumption of `Init.lean`'s); and `ErrExist` holds a non-nil error (io/fs's, which the initializer
copies; `wal.Create` returns it, 2026-11-14), `ErrNotExist` holds an `*errorString` for good (`wal.Exist`
compares with it, 2026-11-14; its type since `wal-vsnap4`; internal/oserror's `ErrNotExist`, which io/fs's holds
too, since 2026-11-22: `errors.IsPathErrnoNotExist.spec`), and so does `ErrInvalid` (the nil-receiver `(*File).Close` returns it,
`WAL.Close` of a nil `dirFile`, 2026-11-14); `checkWrapErr` (a translated `var` only os's tests set) holds `false`
for good (`(*File).wrapErr` of an error reads it: `io.CopyFiles.spec`'s proof, 2026-11-22). -/
instance os_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.os :=
  define_is_pkg_init iprop((∃ f : Loc, typedPointsto (globalAddr os.Stderr) f DFrac.discard) ∗
    (∃ e : GoInterface, ⌜e ≠ interface.nil⌝ ∗ typedPointsto (globalAddr os.ErrExist) e DFrac.discard) ∗
    (∃ x : Loc, typedPointsto (globalAddr os.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard ∗
      typedPointsto (globalAddr _root_.Perennial.internal.oserror.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard) ∗
    (∃ e : GoInterface, typedPointsto (globalAddr os.ErrInvalid) e DFrac.discard) ∗
    (∃ e : GoInterface, EtcdGrove.fmtErrorOk e ∗ typedPointsto (globalAddr os.ErrClosed) e DFrac.discard) ∗
    typedPointsto (globalAddr os.checkWrapErr) false DFrac.discard ∗
    -- (featuregate-3, 2026-11-23) `Args` holds some `[]string`, read-only for good (`init.0`'s
    -- `Args = runtime_args()`): `flag`'s `init` reads `os.Args[0]` when it is non-empty
    (∃ (s : GoSlice) (xs : List GoString),
      typedPointsto (globalAddr os.Args) s DFrac.discard ∗ s ↦*{DFrac.discard} xs))
instance os_get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.os :=
  build_get_is_pkg_init_wf

/-- `os.ErrExist` holds a non-nil error, for good (the part's fact). -/
theorem errExist_of_pkgInit : isPkgInit (PROP := IProp GF) pkg_id.os ⊢
    ∃ e : GoInterface, ⌜e ≠ interface.nil⌝ ∗
      typedPointsto (globalAddr os.ErrExist) e DFrac.discard := by
  refine (isPkgInit_access (PROP := IProp GF) pkg_id.os).trans ?_
  show iprop((∃ f : Loc, typedPointsto (globalAddr os.Stderr) f DFrac.discard) ∗
      (∃ e : GoInterface, ⌜e ≠ interface.nil⌝ ∗ typedPointsto (globalAddr os.ErrExist) e DFrac.discard) ∗
      (∃ x : Loc, typedPointsto (globalAddr os.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard ∗
      typedPointsto (globalAddr _root_.Perennial.internal.oserror.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard) ∗
      (∃ e : GoInterface, typedPointsto (globalAddr os.ErrInvalid) e DFrac.discard) ∗
      (∃ e : GoInterface, EtcdGrove.fmtErrorOk e ∗
        typedPointsto (globalAddr os.ErrClosed) e DFrac.discard) ∗
      typedPointsto (globalAddr os.checkWrapErr) false DFrac.discard ∗
      (∃ (s : GoSlice) (xs : List GoString),
        typedPointsto (globalAddr os.Args) s DFrac.discard ∗ s ↦*{DFrac.discard} xs)) ⊢ _
  iintro ⟨-, He, -, -, -, -, -⟩
  iexact He

/-- `os.ErrNotExist` holds some error, for good (the part's fact). -/
theorem errNotExist_of_pkgInit : isPkgInit (PROP := IProp GF) pkg_id.os ⊢
    ∃ e : GoInterface, typedPointsto (globalAddr os.ErrNotExist) e DFrac.discard := by
  refine (isPkgInit_access (PROP := IProp GF) pkg_id.os).trans ?_
  show iprop((∃ f : Loc, typedPointsto (globalAddr os.Stderr) f DFrac.discard) ∗
      (∃ e : GoInterface, ⌜e ≠ interface.nil⌝ ∗ typedPointsto (globalAddr os.ErrExist) e DFrac.discard) ∗
      (∃ x : Loc, typedPointsto (globalAddr os.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard ∗
      typedPointsto (globalAddr _root_.Perennial.internal.oserror.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard) ∗
      (∃ e : GoInterface, typedPointsto (globalAddr os.ErrInvalid) e DFrac.discard) ∗
      (∃ e : GoInterface, EtcdGrove.fmtErrorOk e ∗
        typedPointsto (globalAddr os.ErrClosed) e DFrac.discard) ∗
      typedPointsto (globalAddr os.checkWrapErr) false DFrac.discard ∗
      (∃ (s : GoSlice) (xs : List GoString),
        typedPointsto (globalAddr os.Args) s DFrac.discard ∗ s ↦*{DFrac.discard} xs)) ⊢ _
  iintro ⟨-, -, ⟨%x, #He, -⟩, -, -, -, -⟩
  iexists _
  iexact He

/-- `os.ErrNotExist` holds an `*errorString`, for good (the part's fact; internal/oserror's `errors.New`,
which `io/fs` and `os` copy: 2026-11-14, `wal-vsnap4`, so that `errors.Is(_, os.ErrNotExist)` is a call on a
pointer target, `errIsTerm`). -/
theorem errNotExist_ptr_of_pkgInit : isPkgInit (PROP := IProp GF) pkg_id.os ⊢
    ∃ x : Loc, typedPointsto (globalAddr os.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard := by
  refine (isPkgInit_access (PROP := IProp GF) pkg_id.os).trans ?_
  show iprop((∃ f : Loc, typedPointsto (globalAddr os.Stderr) f DFrac.discard) ∗
      (∃ e : GoInterface, ⌜e ≠ interface.nil⌝ ∗ typedPointsto (globalAddr os.ErrExist) e DFrac.discard) ∗
      (∃ x : Loc, typedPointsto (globalAddr os.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard ∗
      typedPointsto (globalAddr _root_.Perennial.internal.oserror.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard) ∗
      (∃ e : GoInterface, typedPointsto (globalAddr os.ErrInvalid) e DFrac.discard) ∗
      (∃ e : GoInterface, EtcdGrove.fmtErrorOk e ∗
        typedPointsto (globalAddr os.ErrClosed) e DFrac.discard) ∗
      typedPointsto (globalAddr os.checkWrapErr) false DFrac.discard ∗
      (∃ (s : GoSlice) (xs : List GoString),
        typedPointsto (globalAddr os.Args) s DFrac.discard ∗ s ↦*{DFrac.discard} xs)) ⊢ _
  iintro ⟨-, -, ⟨%x, #He, -⟩, -, -, -, -⟩
  iexists x
  iexact He

/-- `os.ErrNotExist` holds internal/oserror's `ErrNotExist` error, for good (the part's fact: `io/fs` and `os`
copy it; 2026-11-22, `errors.IsPathErrnoNotExist.spec`'s proof: `syscall.Errno.Is` compares its target with
internal/oserror's variable). -/
theorem errNotExist_oserror_of_pkgInit : isPkgInit (PROP := IProp GF) pkg_id.os ⊢
    ∃ x : Loc, typedPointsto (globalAddr os.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard ∗
      typedPointsto (globalAddr _root_.Perennial.internal.oserror.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard := by
  refine (isPkgInit_access (PROP := IProp GF) pkg_id.os).trans ?_
  show iprop((∃ f : Loc, typedPointsto (globalAddr os.Stderr) f DFrac.discard) ∗
      (∃ e : GoInterface, ⌜e ≠ interface.nil⌝ ∗ typedPointsto (globalAddr os.ErrExist) e DFrac.discard) ∗
      (∃ x : Loc, typedPointsto (globalAddr os.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard ∗
      typedPointsto (globalAddr _root_.Perennial.internal.oserror.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard) ∗
      (∃ e : GoInterface, typedPointsto (globalAddr os.ErrInvalid) e DFrac.discard) ∗
      (∃ e : GoInterface, EtcdGrove.fmtErrorOk e ∗
        typedPointsto (globalAddr os.ErrClosed) e DFrac.discard) ∗
      typedPointsto (globalAddr os.checkWrapErr) false DFrac.discard ∗
      (∃ (s : GoSlice) (xs : List GoString),
        typedPointsto (globalAddr os.Args) s DFrac.discard ∗ s ↦*{DFrac.discard} xs)) ⊢ _
  iintro ⟨-, -, He, -, -, -, -⟩
  iexact He

/-- `os.ErrInvalid` holds some error, for good (the part's fact). -/
theorem errInvalid_of_pkgInit : isPkgInit (PROP := IProp GF) pkg_id.os ⊢
    ∃ e : GoInterface, typedPointsto (globalAddr os.ErrInvalid) e DFrac.discard := by
  refine (isPkgInit_access (PROP := IProp GF) pkg_id.os).trans ?_
  show iprop((∃ f : Loc, typedPointsto (globalAddr os.Stderr) f DFrac.discard) ∗
      (∃ e : GoInterface, ⌜e ≠ interface.nil⌝ ∗ typedPointsto (globalAddr os.ErrExist) e DFrac.discard) ∗
      (∃ x : Loc, typedPointsto (globalAddr os.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard ∗
      typedPointsto (globalAddr _root_.Perennial.internal.oserror.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard) ∗
      (∃ e : GoInterface, typedPointsto (globalAddr os.ErrInvalid) e DFrac.discard) ∗
      (∃ e : GoInterface, EtcdGrove.fmtErrorOk e ∗
        typedPointsto (globalAddr os.ErrClosed) e DFrac.discard) ∗
      typedPointsto (globalAddr os.checkWrapErr) false DFrac.discard ∗
      (∃ (s : GoSlice) (xs : List GoString),
        typedPointsto (globalAddr os.Args) s DFrac.discard ∗ s ↦*{DFrac.discard} xs)) ⊢ _
  iintro ⟨-, -, -, He, -, -, -⟩
  iexact He

/-- `os.ErrClosed` holds an error `fmt` formats, for good (the part's fact). -/
theorem errClosed_of_pkgInit : isPkgInit (PROP := IProp GF) pkg_id.os ⊢
    ∃ e : GoInterface, EtcdGrove.fmtErrorOk e ∗
      typedPointsto (globalAddr os.ErrClosed) e DFrac.discard := by
  refine (isPkgInit_access (PROP := IProp GF) pkg_id.os).trans ?_
  show iprop((∃ f : Loc, typedPointsto (globalAddr os.Stderr) f DFrac.discard) ∗
      (∃ e : GoInterface, ⌜e ≠ interface.nil⌝ ∗ typedPointsto (globalAddr os.ErrExist) e DFrac.discard) ∗
      (∃ x : Loc, typedPointsto (globalAddr os.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard ∗
      typedPointsto (globalAddr _root_.Perennial.internal.oserror.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard) ∗
      (∃ e : GoInterface, typedPointsto (globalAddr os.ErrInvalid) e DFrac.discard) ∗
      (∃ e : GoInterface, EtcdGrove.fmtErrorOk e ∗
        typedPointsto (globalAddr os.ErrClosed) e DFrac.discard) ∗
      typedPointsto (globalAddr os.checkWrapErr) false DFrac.discard ∗
      (∃ (s : GoSlice) (xs : List GoString),
        typedPointsto (globalAddr os.Args) s DFrac.discard ∗ s ↦*{DFrac.discard} xs)) ⊢ _
  iintro ⟨-, -, -, -, He, -, -⟩
  iexact He

/-- `os.checkWrapErr` holds `false`, for good. -/
theorem checkWrapErr_of_pkgInit : isPkgInit (PROP := IProp GF) pkg_id.os ⊢
    typedPointsto (globalAddr os.checkWrapErr) false DFrac.discard := by
  refine (isPkgInit_access (PROP := IProp GF) pkg_id.os).trans ?_
  show iprop((∃ f : Loc, typedPointsto (globalAddr os.Stderr) f DFrac.discard) ∗
      (∃ e : GoInterface, ⌜e ≠ interface.nil⌝ ∗ typedPointsto (globalAddr os.ErrExist) e DFrac.discard) ∗
      (∃ x : Loc, typedPointsto (globalAddr os.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard ∗
      typedPointsto (globalAddr _root_.Perennial.internal.oserror.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard) ∗
      (∃ e : GoInterface, typedPointsto (globalAddr os.ErrInvalid) e DFrac.discard) ∗
      (∃ e : GoInterface, EtcdGrove.fmtErrorOk e ∗
        typedPointsto (globalAddr os.ErrClosed) e DFrac.discard) ∗
      typedPointsto (globalAddr os.checkWrapErr) false DFrac.discard ∗
      (∃ (s : GoSlice) (xs : List GoString),
        typedPointsto (globalAddr os.Args) s DFrac.discard ∗ s ↦*{DFrac.discard} xs)) ⊢ _
  iintro ⟨-, -, -, -, -, He, -⟩
  iexact He

/-- `os.Args` holds some `[]string`, read-only for good (featuregate-3, 2026-11-23: `flag`'s `init`). -/
theorem args_of_pkgInit : isPkgInit (PROP := IProp GF) pkg_id.os ⊢
    ∃ (s : GoSlice) (xs : List GoString),
      typedPointsto (globalAddr os.Args) s DFrac.discard ∗ s ↦*{DFrac.discard} xs := by
  refine (isPkgInit_access (PROP := IProp GF) pkg_id.os).trans ?_
  show iprop((∃ f : Loc, typedPointsto (globalAddr os.Stderr) f DFrac.discard) ∗
      (∃ e : GoInterface, ⌜e ≠ interface.nil⌝ ∗ typedPointsto (globalAddr os.ErrExist) e DFrac.discard) ∗
      (∃ x : Loc, typedPointsto (globalAddr os.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard ∗
      typedPointsto (globalAddr _root_.Perennial.internal.oserror.ErrNotExist)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard) ∗
      (∃ e : GoInterface, typedPointsto (globalAddr os.ErrInvalid) e DFrac.discard) ∗
      (∃ e : GoInterface, EtcdGrove.fmtErrorOk e ∗
        typedPointsto (globalAddr os.ErrClosed) e DFrac.discard) ∗
      typedPointsto (globalAddr os.checkWrapErr) false DFrac.discard ∗
      (∃ (s : GoSlice) (xs : List GoString),
        typedPointsto (globalAddr os.Args) s DFrac.discard ∗ s ↦*{DFrac.discard} xs)) ⊢ _
  iintro ⟨-, -, -, -, -, -, He⟩
  iexact He

end os

end init

end Perennial
