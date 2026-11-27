/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/newCountingReader.lean (241f27e).
-/
/-
The proof of `raft.newCountingReader` (stage 3, snap).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.newCountingReader
public import Perennial.Proof.sync.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto gprot

theorem github_com.hashicorp.raft.newCountingReader.wp_proof :
    github_com.hashicorp.raft.newCountingReader.spec (GF := GF) (hG := hG) := by
  intro rd
  wp_start
  iapply wp_fupd
  wp_auto
  iStructNamed «$r0»
  ipersist reader
  imod sync.init_Mutex (iprop(∃ n : w64, «$r0_ptr».[countingReader, go!"bytes"] ↦ n)) ⊤ _ $$ mu [bytes]
    with #Hmu
  · iexists _; iexact bytes
  imodintro
  iapply HΦ
  unfold countingReaderIs
  iframe #

end proof

end Perennial
