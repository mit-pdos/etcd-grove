/-
Package `replica`'s results: the server's boot specs (`Replica.lean`), over the proxy's entry
points (premises: package `proxy`'s results, `Proxy/`) and the hypotheses (`Hyp.lean`: gRPC,
math/rand, strconv.Atoi, sync.Map).

Changed against the lab: its `src_initialize'` (`raxos/replica/src`'s initialization from its
imports', over `Replica/{Init,Inits,HarnessInit}.lean`) is the generated
`raxos.replica.src.wp_initialize'` (`Dsverify/Proof/raxos/replica/src/Init.lean`, whose package
fact is `srcState`) with the names-only libraries' `InitHyp`s; those three files are not ported.
-/
module

public import Dsverify.Proof.raxos.Replica.Server

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

theorem New.wp_proof [MapHyp qv.map] [hyp.grpc.GrpcHyp (cd := hyp.qpCodec) qv.grpc]
    [hyp.RandHyp GF] [hyp.AtoiHyp GF] (hNP : NewProxy.spec (GF := GF) (hG := hG)) :
    New.spec (GF := GF) (hG := hG) :=
  wp_New hNP

theorem Server.NetworkInit.wp_proof [hyp.grpc.GrpcHyp (cd := hyp.qpCodec) qv.grpc]
    [hyp.RandHyp GF] [hyp.AtoiHyp GF] (hNI : Proxy.NetworkInit.spec (GF := GF) (hG := hG)) :
    Server.NetworkInit.spec (GF := GF) (hG := hG) :=
  wp_Server_NetworkInit hNI

theorem Server.StartProposers.wp_proof [hyp.grpc.GrpcHyp (cd := hyp.qpCodec) qv.grpc]
    [hyp.RandHyp GF] [hyp.AtoiHyp GF] :
    Server.StartProposers.spec (GF := GF) (hG := hG) :=
  wp_Server_StartProposers

theorem Server.Run.wp_proof [hyp.grpc.GrpcHyp (cd := hyp.qpCodec) qv.grpc]
    [hyp.RandHyp GF] [hyp.AtoiHyp GF] (hRun : Proxy.Run.spec (GF := GF) (hG := hG)) :
    Server.Run.spec (GF := GF) (hG := hG) :=
  wp_Server_Run hRun

end results

end Perennial.raxos
