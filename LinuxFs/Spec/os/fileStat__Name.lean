/-
`fs.Name()` on the `*fileStat` that `(*os.File).Stat`, `os.Stat` or `os.Lstat` returns: some string.
`Name` is translated (`return fs.name`) over the model's layout of `fileStat`, whose `name` the models
set to the base name of the path (`model.base`; 2026-11-13, pending the user's review,
`examples/osfs/semantics/model_os_filestat_name.go`). Used by the WAL's `os.File`-reader bridge (the
decoder's "frame too large" error). Proved in `Proof/os/fileStat__Name.lean`. Lean-first.
-/
module

public import LinuxFs.Proof.os.Base

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
abbrev os.fileStat.Name.spec : Prop :=
  ∀ (fs : Loc) (sz : w64),
  {{ os.ownFileStat (GF := GF) fs sz }}
    (App (Val (fs @!! go.GoType.PointerType os.fileStat.ty @!! go!"Name")) (Val #()))
  {{ (s : GoString), RET #s; os.ownFileStat fs sz }}

end spec

end EtcdGrove
end Perennial
