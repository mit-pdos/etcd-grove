/-
Package `proposer`'s results (interface statements of stage 2), proved from the package's
internal specs (`Proposer/Run.lean`).
-/
module

public import Dsverify.Proof.raxos.Wire
public import Dsverify.Proof.raxos.Replica
public import Dsverify.Proof.raxos.Proposer.Run

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open models_lab.pbcodec (PbCodec)

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

theorem NewProposer.wp_proof [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions] [raxos.examples.quepaxanet.Assumptions] [hyp.grpc.GrpcHyp (cd := hyp.qpCodec) qv.grpc] [hyp.RandHyp GF] : NewProposer.spec (GF := GF) (hG := hG) := by
  exact prop.wp_NewProposer

theorem Proposer.runProposer.wp_proof [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions] [raxos.examples.quepaxanet.Assumptions] [hyp.grpc.GrpcHyp (cd := hyp.qpCodec) qv.grpc] [hyp.RandHyp GF] : Proposer.runProposer.spec (GF := GF) (hG := hG) := by
  intro γ c k p
  exact prop.wp_runProposer γ c k p

end results

end Perennial.raxos

