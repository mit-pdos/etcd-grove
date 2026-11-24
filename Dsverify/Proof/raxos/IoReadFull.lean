/-
`raxos.ioLt.ReadAtLeast`/`raxos.ioLt.ReadFull`: Perennial's proofs (`io.ReadAtLeast.wp_proof`,
`io.ReadFull.wp_proof`). Until the pin bump to Perennial `580868e54` (2026-11-24) these were local
copies of Perennial branch `readatleast-prefix` (`af905abba`), whose specs ask the reader's
condition only of the reads made (a connection's, `net.conn_readerOk`, refuses an empty read); that
branch is now in Perennial `lean`.
-/

module

public import Dsverify.Proof.raxos.IoReadFullSpec
public import Perennial.Proof.io.ReadAtLeast
public import Perennial.Proof.io.ReadFull

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

theorem raxos.ioLt.ReadAtLeast.wp_proof :
    raxos.ioLt.ReadAtLeast.spec (GF := GF) (hG := hG) :=
  io.ReadAtLeast.wp_proof

theorem raxos.ioLt.ReadFull.wp_proof
    (wp_ReadAtLeast : raxos.ioLt.ReadAtLeast.spec (GF := GF) (hG := hG)) :
    raxos.ioLt.ReadFull.spec (GF := GF) (hG := hG) :=
  io.ReadFull.wp_proof wp_ReadAtLeast

end proof

end Perennial
