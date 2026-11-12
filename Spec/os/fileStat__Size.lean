/-
`fs.Size()` on the `*fileStat` that `(*os.File).Stat` returns (this repository's `os`, project
`bboltfs`): its size. `Size` is translated (`return fs.size`), over the model's layout of
`fileStat`. Proved in `Proof/os/fileStat__Size.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- See the file header. -/
abbrev os.fileStat.Size.spec : Prop :=
  ∀ (fs : Loc) (sz : w64),
  {{ os.ownFileStat (GF := GF) fs sz }}
    (App (Val (fs @!! go.GoType.PointerType os.fileStat.ty @!! go!"Size")) (Val #()))
  {{ RET #sz; os.ownFileStat fs sz }}

end spec

end EtcdGrove
end Perennial
