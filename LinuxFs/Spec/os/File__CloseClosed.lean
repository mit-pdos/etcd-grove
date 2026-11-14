/-
`f.Close()` on a closed `*os.File` (fd -1, after an earlier `Close`; this repository's `os`, project
`bboltfs`): Go's `file.close` finds the `poll.FD` closing (`pfd.Close`'s `incref` fails with
`ErrFileClosing`) and returns `&PathError{"close", name, ErrClosed}`, changing nothing. The `*File`
keeps its name and its fd field -1.

**Not proved: the trusted model does not cover it.** `File.Close.impl` (`TrustedCode/os.lean`) asks the
extension `FdKind(-1)`, which is stuck on an fd that is not open (`GooseLang/Ext/Fs/Impl.lean`); the
model's header lists a closed file among what it leaves undefined. The WAL's `Create` reaches it (W4
log, nineteenth session): after `renameWALUnlock`'s `w.Close()` closed the locks and its rename failed,
`Create`'s deferred `f.Close()` closes the segment's file again. A hypothesis of `wal.Create.wp_proof`
until the model returns Go's error on fd -1 (a trusted change, proposed in `notes/wal-fsext-plan.md`, W4
log, nineteenth session; pending the user's review). Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.os.Base
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
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f (-1 : w64) name (DFrac.own 1) }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; os.ownFile f (-1 : w64) name (DFrac.own 1) ∗
      fmtErrorOkOrNil err }}

end spec

end EtcdGrove
end Perennial
