/-
Package `proxy`: `Proxy.Run`'s proof, linked from its pieces (`RunDefs.lean` states them):
`wp_Run` (`RunLoop.lean`) over the handlers, each over the specs of what it calls.
-/
module

public import Dsverify.Proof.raxos.Proxy.RunLoop
public import Dsverify.Proof.raxos.Proxy.RunFetch
public import Dsverify.Proof.raxos.Proxy.RunTimer
public import Dsverify.Proof.raxos.Proxy.RunNotify
public import Dsverify.Proof.raxos.Proxy.RunClientBatch2
public import Dsverify.Proof.raxos.Proxy.RunPropose
public import Dsverify.Proof.raxos.Proxy.RunDecide
public import Dsverify.Proof.raxos.Proxy.RunRecorder

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-- `pr.Run()` (`Proxy.Run.spec`), from leader mode 2's `calculateSequence` and
`updateEpochTime` (`MabCalc.lean`). -/
theorem run_proof_of
    [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions] [hyp.AtoiSpec GF]
    (wp_calc : calculateSequence_spec (GF := GF) (hG := hG))
    (wp_uet : updateEpochTime_spec (GF := GF) (hG := hG)) : Proxy.Run.spec (GF := GF) (hG := hG) :=
  wp_Run
    (wp_handleClientBatch wp_NewTimerWithCancel wp_SetTimeoutFuntion wp_Start
      wp_getLeaderSequence wp_getLeaderWait wp_handleDecisionNotification)
    (wp_proposeToIndex (wp_proposePreviousEpochSummary wp_calc))
    (wp_handleProposeResponse wp_uet) (wp_handleRecorderResponse wp_uet) wp_handleFetchResponse

end proofs

end Perennial.raxos
