/-
`f.Close()` on a nil `*os.File` (this repository's `os`, project `bboltfs`): the model
(`TrustedCode/os.lean`, `File.Close.impl`) returns `os.ErrInvalid` without a system call (Go's
`file_posix.go`: `if f == nil { return ErrInvalid }`; Go example
`examples/osfs/semantics/model_os_close_nil.go`). `WAL.Close` of a WAL whose `dirFile` is nil (`Open`'s
error path, `renameWALUnlock`'s) reaches it. The error is some error: `os`'s package fact records the
variable `ErrInvalid` (`Proof/os/PkgInit.lean`). Proved in `Proof/os/File__CloseNil.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import LinuxFs.Proof.os.Base
public import LinuxFs.Proof.os.PkgInit

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
abbrev os.File.Close.specNil : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.os }}
    (App (Val ((null : Loc) @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
