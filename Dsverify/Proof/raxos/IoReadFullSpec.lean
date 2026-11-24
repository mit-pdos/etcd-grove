/-
The statements of `raxos.ioLt.ReadAtLeast`/`raxos.ioLt.ReadFull` (`IoReadFull.lean` proves them;
split off so that the proofs that call them import no proof module: CLAUDE.md, "Import tiers").
Until the pin bump to Perennial `580868e54` (2026-11-24) these were local copies of Perennial
branch `readatleast-prefix` (`af905abba`: `Pre` asked only of the reads made); that branch is now in
Perennial `lean`, so each is Perennial's spec under the old name.
-/
module

public import Perennial.Spec.io.ReadAtLeast
public import Perennial.Spec.io.ReadFull

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

/-- Perennial's `io.ReadAtLeast.spec` (the reader's condition `Pre` asked only of the reads made,
never of an empty one). -/
abbrev raxos.ioLt.ReadAtLeast.spec : Prop := io.ReadAtLeast.spec (GF := GF) (hG := hG)

/-- Perennial's `io.ReadFull.spec` (the reader's condition `Pre` asked only of the reads made,
never of an empty one). -/
abbrev raxos.ioLt.ReadFull.spec : Prop := io.ReadFull.spec (GF := GF) (hG := hG)

end spec

end Perennial
