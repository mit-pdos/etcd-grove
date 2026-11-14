/-
`f.Close()` on a closed `*os.File` (fd -1, after an earlier `Close`; this repository's `os`, project
`bboltfs`): Go's `file.close` finds the `poll.FD` closing (`pfd.Close`'s `incref` fails with
`ErrFileClosing`) and returns `&PathError{"close", name, ErrClosed}`, changing nothing. The `*File`
keeps its name and its fd field -1.

The model (`File.Close.impl`, `TrustedCode/os.lean`) returns that error on fd -1 without a system call
(2026-11-14, pending the user's review; Go example `examples/osfs/semantics/model_os_close_twice.go`).
The error is `os.ErrClosed`, which the package's initialization gives (`os.errClosed_of_pkgInit`). The
WAL's `Create` reaches it (`notes/wal-fsext-plan.md`, W4 log, nineteenth session): after
`renameWALUnlock`'s `w.Close()` closed the locks and its rename failed, `Create`'s deferred `f.Close()`
closes the segment's file again. Proved in `Proof/os/File__CloseClosed.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import LinuxFs.Proof.os.Base
public import LinuxFs.Proof.os.PkgInit
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- See the file header. -/
abbrev os.File.Close.specClosed : Prop :=
  ∀ (f : Loc) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗
      os.ownFile (GF := GF) f (-1 : w64) name (DFrac.own 1) }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; os.ownFile f (-1 : w64) name (DFrac.own 1) ∗
      fmtErrorOkOrNil err }}

end spec

end EtcdGrove
end Perennial
