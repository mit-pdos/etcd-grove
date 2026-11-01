/-
Shared definitions of the specs of `os`'s trusted models (`TrustedCode/os.lean`, this repository's
`os`, project `bboltfs`): the typed points-to of the model's `file` and `fileStat`, and the
resource of an open `*os.File` (`ownFile`).

The model's `file` and `fileStat` are trusted types (`Code/os.toml`); goose emits no field-access
assumptions for them (`file.TypeAssumptions` has no `get_fd`/`set_fd`, unlike `File`'s
`get_file`), so they have no typed points-to of the whole struct, and a `GoAlloc` of one (in
`OpenFile` and `Stat`) cannot be reasoned about. Their fields are owned one by one
(`structFieldRef os.file go!"fd" inner ↦ fd`), which is all that loads and stores need.
-/
module

public import GeneratedProof.os
public import Proof.syscall.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace os

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : os.Assumptions]

theorem file_ty_eq : os.model.file = os.file.ty := by
  unfold os.file.ty; rfl

theorem File_ty_eq : os.model.File = os.File.ty := by
  unfold os.File.ty; rfl

theorem fileStat_ty_eq : os.model.fileStat = os.fileStat.ty := by
  unfold os.fileStat.ty; rfl

include sem package_sem' in
/-- The `*os.File` `f` is open on the fd `fd`, named `name`: `f` points to a `File` whose inner
`file` holds the fd (a fraction `dq` of it: `Close` writes it) and the name. -/
def ownFile (f : Loc) (fd : w64) (name : GoString) (dq : DFrac) : IProp GF :=
  iprop(∃ inner : Loc, f ↦□ (os.File.mk inner) ∗
    structFieldRef os.file go!"fd" inner ↦{dq} fd ∗
    structFieldRef os.file go!"name" inner ↦□ name)

end def_
end os

end Perennial
