/- Lean-first (no Rocq counterpart).

# The examples' extension: none that does anything (2026-10-26)

Perennial's semantics runs a program against a closed list of GooseLang extensions (Perennial
`4ce1bd4da`, `GooseLang/Ext.lean`), which replaced the single FFI. The examples use no extension
operation: their proofs are generic over the list (`[GooseExts] [GooseSemantics] [GooseInterp]`),
and their closed theorems (`examples/*/Adequacy.lean`) close it as `[trivialExt]`, an extension
with no operations, no values and no state, whose ghost state is trivial. (Before, they closed it
with the disk FFI, whose operations they did not use either; Perennial removed it, `7b607280f`.)

A stand-in until the examples use a real extension (a network, a filesystem): an extension with
no operations adds no step, so the semantics of `[trivialExt]` is GooseLang's alone.
-/
module

public import Perennial.GooseLang.Adequacy

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- The extension with no operations, no values and no state. -/
@[reducible] def trivialExt : GooseExt where
  name := "github.com/mit-pdos/etcd-grove/examples/common.trivialExt"
  Val := Empty
  LocalState := Unit
  GlobalState := Unit

/-- It never steps (it has no operation) and survives a crash unchanged. -/
instance trivial_semantics : ExtSemantics trivialExt where
  step _ _ _ _ _ _ _ _ _ := False
  crash _ _ := True

/-- Its ghost state: none. -/
instance trivial_interp : ExtInterp trivialExt where
  LocalGS _ := Unit
  GlobalGS _ := Unit
  localCtx _ _ := iprop(True)
  globalCtx _ _ := iprop(True)
  PreG _ := Unit
  initgP _ := True
  initP _ _ := True
  globalStart _ _ := iprop(True)
  localStart _ _ := iprop(True)
  global_init _ _ _ _ := by
    iapply bupd_intro; iexists (); isplitl [] <;> itrivial
  local_init _ _ _ _ _ := by
    iapply bupd_intro; iexists (); isplitl [] <;> itrivial

/-- The examples' extensions: `trivialExt` alone. -/
@[reducible] def trivialExts : GooseExts := ⟨[trivialExt]⟩

attribute [local instance] trivialExts

@[reducible] def trivialExtsSemantics : GooseSemantics := ⟨(trivial_semantics, ⟨⟩)⟩

@[reducible] def trivialExtsInterp : GooseInterp := ⟨(trivial_interp, ⟨⟩)⟩

end EtcdGrove
end Perennial
