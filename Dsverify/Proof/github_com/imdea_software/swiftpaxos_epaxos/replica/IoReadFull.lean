/-
`ioReadAtLeastPre`/`ioReadFullPre`: Perennial's proofs (`io.ReadAtLeast.wp_proof`,
`io.ReadFull.wp_proof`). Until the pin bump to Perennial `580868e54` (2026-11-24) these were local
copies of Perennial branch `readatleast-prefix` (`af905abba`; `notes/perennial-changes.md`,
2026-11-23, "`io.ReadFull`/`io.ReadAtLeast` ask `Pre` of a read they never make"), now in Perennial
`lean`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.IoReadFullPre
public import Perennial.Proof.io.ReadAtLeast
public import Perennial.Proof.io.ReadFull

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

theorem ioReadAtLeastPre.wp_proof :
    ioReadAtLeastPre.spec (GF := GF) (hG := hG) :=
  io.ReadAtLeast.wp_proof

theorem ioReadFullPre.wp_proof
    (wp_ReadAtLeast : ioReadAtLeastPre.spec (GF := GF) (hG := hG)) :
    ioReadFullPre.spec (GF := GF) (hG := hG) :=
  io.ReadFull.wp_proof wp_ReadAtLeast

end spec

end Perennial
