/-
Package `proxy`'s results: its entry points' specs (`Replica.lean`), over the hypotheses
(`Hyp.lean`): `Proxy.Run.spec` (leader mode 2: `calculateSequence`'s `sort.Ints` and
`strconv.FormatInt`, `updateEpochTime`'s `time`), `NewProxy.spec` (`newProxy_proof`) and
`Proxy.NetworkInit.spec` (`networkInit_of` with the accept routine `waitForConnections_of` over
`net`'s, `io.ReadFull`'s (`IoReadFull.lean`) and `bufio.NewReader`'s proofs, and the routines
`connectionListener_proof`, `connectToClient_proof`, `startOutgoingLinks_proof`).
-/
module

public import Dsverify.Proof.raxos.Proxy.Run
public import Dsverify.Proof.raxos.AtoiProof
public import Dsverify.Proof.raxos.Proxy.MabCalc
public import Dsverify.Proof.raxos.Proxy.NewProxy
public import Dsverify.Proof.raxos.Proxy.NetInit
public import Dsverify.Proof.raxos.Proxy.NetAccept
public import Dsverify.Proof.raxos.Proxy.NetDial
public import Dsverify.Proof.raxos.Proxy.NetListen
public import Dsverify.Proof.raxos.Proxy.NetSend
public import Net.Proof.net.Listen
public import Net.Proof.net.Listener__Accept
public import Net.Proof.net.Conn__Read
public import Net.Proof.net.Conn__Close
public import Proof.bufio.NewReaderOk
public import Proof.bufio.NewReaderSize

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
variable [strconv.Assumptions] [time.Assumptions] [fmt.Assumptions]

/-- `pr.Run()`, the proxy's main loop. -/
theorem Proxy.Run.wp_proof [hyp.SortHyp GF] :
    Proxy.Run.spec (GF := GF) (hG := hG) :=
  run_proof_of (wp_calculateSequence wp_getLeaderSequence) (wp_updateEpochTime wp_hasAllDecided)

/-- `NewProxy(...)`, the proxy's constructor. -/
theorem NewProxy.wp_proof [hyp.UtcHyp GF] [hyp.RandHyp GF] :
    NewProxy.spec (GF := GF) (hG := hG) :=
  newProxy_proof

/-- `pr.NetworkInit()`: the links to the clients and the accept routine. -/
theorem Proxy.NetworkInit.wp_proof [hyp.PrintlnHyp GF] [hyp.PbHyp GF]
    [_root_.Perennial.bufio.Assumptions] [_root_.Perennial.io.Assumptions] [errors.Assumptions]
    [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj] :
    Proxy.NetworkInit.spec (GF := GF) (hG := hG) :=
  networkInit_of
    (waitForConnections_of net.Listen.wp_proof net.Listener.Accept.wp_proof net.Conn.Read.wp_proof
      net.Conn.Close.wp_proof (raxos.ioLt.ReadFull.wp_proof raxos.ioLt.ReadAtLeast.wp_proof)
      (EtcdGrove.bufio.NewReader.wp_proofOk
        (EtcdGrove.bufio.NewReader.wp_proofE EtcdGrove.bufio.NewReaderSize.wp_proofE))
      connectionListener_proof connectToClient_proof)
    startOutgoingLinks_proof

end results

end Perennial.raxos
