/-
`fs.Name()` on the `*fileStat` that `(*os.File).Stat` returns: some string. **No proof**: the
trusted `os` model's `fileStat` has no `name` field and `Name` no body (its method set lists it, with
no unfold), so a call is stuck. Go's is `return fs.name` (`types_unix.go`), the base name `Stat`
stored. A hypothesis of the WAL's `os.File`-reader bridge (the decoder's `decFile` asks
`FileInfo().Name()` to return, for its "frame too large" error message); discharging it needs the
model to keep the name (a trusted change: `notes/wal-fsext-plan.md`, W3/W5 log, `wal-read5`).
Lean-first (no Rocq counterpart).
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
