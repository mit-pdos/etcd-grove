/-
The specs `ioReadAtLeastPre.spec`, `ioReadFullPre.spec` of `replica/IoReadFull.lean` (proved there; a
defs module, so that `replica/ServeConn.lean` takes `ioReadFullPre.spec` as a hypothesis,
`EpReplicaDeps`, and `replica/Link.lean` passes the proof: CLAUDE.md, "Import tiers").

Until the pin bump to Perennial `580868e54` (2026-11-24) these were a local workaround of a
Perennial gap (`notes/perennial-changes.md`, 2026-11-23, "`io.ReadFull`/`io.ReadAtLeast` ask `Pre`
of a read they never make"): copies of the specs of Perennial branch `readatleast-prefix`
(`af905abba`: `Pre` only of the reads made), which a connection's reader contract
(`net.conn_readerOk`, `0 < m`) needs. That branch is now in Perennial `lean`, so each is
Perennial's spec under the old name.
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

/-- Perennial's `io.ReadAtLeast.spec`. -/
abbrev ioReadAtLeastPre.spec : Prop := io.ReadAtLeast.spec (GF := GF) (hG := hG)

/-- Perennial's `io.ReadFull.spec`. -/
abbrev ioReadFullPre.spec : Prop := io.ReadFull.spec (GF := GF) (hG := hG)

end spec

end Perennial
