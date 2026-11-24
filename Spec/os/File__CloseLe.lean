/-
`f.Close()` on an open `*os.File`, as `File__Close.lean`, with a bound on the message of the error it
returns: `os.closeErrMax name` bytes, the length of `"close " + name + ": " + Errno(e).Error()`
(`*PathError`'s `Error()`, translated; `Errno.Error`, translated, at most `syscall.errnoMsgMax`
bytes: `Proof/syscall/ErrorOk.lean`). For a caller that collects the messages (the WAL's
`closeAll`, which joins them with `strings.Join`, whose spec bounds its output); `Close`'s other
callers use `File__Close.lean`. Proved in `Proof/os/File__CloseLe.lean`. Lean-first (2026-11-24,
fmt stage 1).
-/
module

public import Proof.os.Base
public import Spec.fmt.ErrorOk
public import GooseLang.Ext.Fs.FsNoErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

/-- The longest message of an error of `Close` on a file named `name`:
`"close " + name + ": " + Errno(e).Error()`. -/
def os.closeErrMax (name : GoString) : Nat := name.length + 8 + syscall.errnoMsgMax

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- See the file header. -/
abbrev os.File.Close.specLe : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (d : OsFd),
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name (DFrac.own 1) ∗
      osFd (GF := GF) fd (DFrac.own 1) d ∗ lockToks (GF := GF) fd d }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err;
      os.ownFile f (-1 : w64) name (DFrac.own 1) ∗ ⌜err = interface.nil ∨ ¬ FsNoErr⌝ ∗
      fmtErrorOkOrNilLe (os.closeErrMax name) err }}

end spec

end EtcdGrove
end Perennial
