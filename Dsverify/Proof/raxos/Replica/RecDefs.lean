/-
Package `replica`'s internal definitions for the recorder (`recorder.go`): the representation of
a recorder's slot states (`slotRep`), its lock invariant (`recInv`, the slots ↔ `recHalf`), and
the recorder's persistent facts (`isRecorder`).
-/
module

public import Dsverify.Proof.raxos.Wire
public import Dsverify.Proof.raxos.Replica.Defs
public import Dsverify.Proof.raxos.Cons.Laws

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-- A fancy update of the global ghost state's invariants (the laws' `|={E}=>`, stated under
`GooseGlobalGS.gooseInvGS`) is the program logic's. -/
theorem fupd_glob (E1 E2 : CoPset) (P : IProp GF) :
    @fupd (IProp GF) (@uPred_fupd_instance GF HasLC.hasLC
      (GooseGlobalGS.gooseInvGS (self := hG.goose_globalGS))) E1 E2 P ⊢ |={E1,E2}=> P := .rfl

end defs

end Perennial.raxos
