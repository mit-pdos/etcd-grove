/- Lean-first (no Rocq counterpart).

# The empty list of extensions

Perennial's semantics runs a program against a closed list of GooseLang extensions
(`GooseLang/Ext.lean`). A program that calls no extension operation can be stated against the
empty list: GooseLang's semantics alone, with no extension state and no extension ghost state.
A statement made at this list says, without a reader having to check which operations the
program calls, that nothing beyond GooseLang (and the trusted models of the Go packages it
imports, its `Assumptions`) is assumed.
-/
module

public import Perennial.GooseLang.Adequacy

@[expose] public section

noncomputable section

namespace Perennial
namespace Robustness

/-- **No extension.** -/
@[reducible] def noExts : GooseExts := ⟨[]⟩

attribute [local instance] noExts

/-- The semantics of no extension: nothing. -/
@[reducible] def noExtsSemantics : GooseSemantics := ⟨PUnit.unit⟩

/-- The ghost state of no extension: nothing. -/
@[reducible] def noExtsInterp : GooseInterp := ⟨PUnit.unit⟩

end Robustness
end Perennial
