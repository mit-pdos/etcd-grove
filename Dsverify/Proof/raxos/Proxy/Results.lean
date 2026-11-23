/-
Package `proxy`'s results: its entry points' specs (`Replica.lean`), over the hypotheses
(`Hyp.lean`). So far `Proxy.Run.spec` (leader mode 2: `calculateSequence`'s `sort.Ints` and
`strconv.FormatInt`, `updateEpochTime`'s `time`); `NewProxy.spec` and `Proxy.NetworkInit.spec`
wait for the ports of the lab's `Proxy/{New*,Net*,WireProof,MsgBuf}.lean` (notes/dsv-quepaxa.md).
-/
module

public import Dsverify.Proof.raxos.Proxy.Run
public import Dsverify.Proof.raxos.Proxy.MabCalc

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : Net.NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
variable [strconv.Assumptions] [time.Assumptions]

/-- `pr.Run()`, the proxy's main loop. -/
theorem Proxy.Run.wp_proof [hyp.AtoiHyp GF] [hyp.SortHyp GF] :
    Proxy.Run.spec (GF := GF) (hG := hG) :=
  run_proof_of (wp_calculateSequence wp_getLeaderSequence) (wp_updateEpochTime wp_hasAllDecided)

end results

end Perennial.raxos
