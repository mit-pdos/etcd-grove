/-
Package `replica`'s results: the server's boot specs (`Replica.lean`), over the proxy's entry
points' proofs (`Proxy/Results`) and the hypotheses (`Hyp.lean`: gRPC, protobuf, math/rand,
sort.Ints, time.UTC, fmt.Println, sync.Map; `strconv.Atoi`'s value spec is proved,
`AtoiProof.lean`).

Changed against the lab: its `src_initialize'` (`raxos/replica/src`'s initialization from its
imports', over `Replica/{Init,Inits,HarnessInit}.lean`) is the generated
`raxos.replica.src.wp_initialize'` (`Dsverify/Proof/raxos/replica/src/Init.lean`, whose package
fact is `srcState`) with the names-only libraries' `InitHyp`s; those three files are not ported.
-/
module

public import Dsverify.Proof.raxos.Replica.Server
public import Dsverify.Proof.raxos.Proxy.Results
public import Dsverify.Proof.raxos.AtoiProof

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open hyp.sync (MapHyp)

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
  [raxos.examples.quepaxanet.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]
variable [strconv.Assumptions] [fmt.Assumptions]

theorem New.wp_proof [MapHyp qv.map] [hyp.grpc.GrpcHyp (cd := hyp.qpCodec) qv.grpc]
    [hyp.RandHyp GF] [hyp.UtcHyp GF] :
    New.spec (GF := GF) (hG := hG) :=
  wp_New NewProxy.wp_proof

theorem Server.NetworkInit.wp_proof [hyp.grpc.GrpcHyp (cd := hyp.qpCodec) qv.grpc]
    [hyp.RandHyp GF] [hyp.PrintlnHyp GF] [hyp.PbHyp GF]
    [_root_.Perennial.bufio.Assumptions] [_root_.Perennial.io.Assumptions] [errors.Assumptions] :
    Server.NetworkInit.spec (GF := GF) (hG := hG) :=
  wp_Server_NetworkInit Proxy.NetworkInit.wp_proof

theorem Server.StartProposers.wp_proof [hyp.grpc.GrpcHyp (cd := hyp.qpCodec) qv.grpc]
    [hyp.RandHyp GF] :
    Server.StartProposers.spec (GF := GF) (hG := hG) :=
  wp_Server_StartProposers

theorem Server.Run.wp_proof [hyp.grpc.GrpcHyp (cd := hyp.qpCodec) qv.grpc]
    [hyp.RandHyp GF] [hyp.SortHyp GF] [time.Assumptions] :
    Server.Run.spec (GF := GF) (hG := hG) :=
  wp_Server_Run Proxy.Run.wp_proof

end results

end Perennial.raxos
