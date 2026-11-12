/-
`f.Fd()` on an open `*os.File` (this repository's `os`, project `bboltfs`): its fd. The model
(`TrustedCode/os.lean`) reads the inner `file`'s `fd`. Proved in `Proof/os/File__Fd.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- See the file header. -/
abbrev os.File.Fd.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dq : DFrac),
  {{ os.ownFile (GF := GF) f fd name dq }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Fd")) (Val #()))
  {{ RET #fd; os.ownFile f fd name dq }}

end spec

end EtcdGrove
end Perennial
