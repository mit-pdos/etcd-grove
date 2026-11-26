/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/Results.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension. `Submit` and `Run` take, as hypotheses, the
`log/slog` logger methods' specs (`LibHyps.lean`: no `log/slog` model here) and the specs of the
two calls into `network` and `events` (`network.TCP.Send.spec`, `events.Event.ToWriter.spec`, at
every JSON codec), until those packages' results are ported; `New` needs none.
-/
/-
The results of `replica`: one theorem per spec of `VsrProof/Spec/replica.lean` (`New`, `Submit`,
`Run` proved in `New.lean`, `SubmitRun.lean`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.replica
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.ConsumeSQ
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.CheckTimers
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.New
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.SubmitRun
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.assert.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.ipv4port.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.queue.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.time.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.log.Logs

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]
variable [models_lab.jsoncodec.JsonCodec GF]

/-- `New.lean`: the members parsed (`FromHostPort`) and sorted (`sort.Sort` through
`ByLess.sorter`, by `ipv4port.portLt`), `NewLogs`, the maps, the queue at `replica.sqElem γ tcp`,
the timers; the facts `committedBy 0 []`, `linPrefix []` by `ghost_fact'`. -/
theorem replica.New.wp : replica.New.spec (GF := GF) (hG := hG) :=
  replica.New.wp_proof ipv4port.IPv4Port.FromHostPort.wp ipv4port.ByLess.sorter.wp
    log.NewLogs.wp_proof queue.New.wp time.NewTimer.wp

/-- `SubmitRun.lean`: `Assert(!running)` (`running = false` in `replica.own`), `sq.Push` with
`sqElem` (the event's first disjunct, from the precondition). -/
theorem replica.Replica.Submit.wp : replica.Replica.Submit.spec (GF := GF) (hG := hG) :=
  replica.Replica.Submit.wp_proof assert.Assert.wp queue.Queue.Push.wp

/-- `SubmitRun.lean`: `Assert(!running)`, `setIsRunning(true)`, the deferred
`setIsRunning(false)`, `replica.wp_consumeSQ` and `replica.wp_checkTimers` (over `replica.ownR`;
`repInv` does not read `running`). Hypotheses: the logger methods (`LibHyps.lean`), `TCP.Send`,
`Event.ToWriter` (at every codec). -/
theorem replica.Replica.Run.wp
    (wp_Debug : log.slog.Logger.Debug.spec (GF := GF) (hG := hG))
    (wp_Info : log.slog.Logger.Info.spec (GF := GF) (hG := hG))
    (wp_Warn : log.slog.Logger.Warn.spec (GF := GF) (hG := hG))
    (wp_Error : log.slog.Logger.Error.spec (GF := GF) (hG := hG))
    (wp_TCP_Send : ∀ [jc : models_lab.jsoncodec.JsonCodec GF],
      network.TCP.Send.spec (GF := GF) (hG := hG))
    (wp_ToWriter : ∀ [jc : models_lab.jsoncodec.JsonCodec GF],
      events.Event.ToWriter.spec (GF := GF) (hG := hG)) :
    replica.Replica.Run.spec (GF := GF) (hG := hG) :=
  replica.Replica.Run.wp_proof ⟨wp_Debug, wp_Info, wp_Warn, wp_Error, wp_TCP_Send, wp_ToWriter,
    assert.Assert.wp, ipv4port.IPv4Port.String.wp, ipv4port.IPv4Port.String_ptr.wp,
    queue.Queue.Push.wp, queue.Queue.Pop.wp, time.NewTimer.wp, time.Timer.Reset.wp,
    time.Timer.Done.wp, time.Timer.SetState.wp, time.Timer.State.wp, log.Logs.Len.wp_proof,
    log.Logs.OpAt.wp_proof, log.Logs.ClientIDAt.wp_proof, log.Logs.RequestIDAt.wp_proof,
    log.Logs.After.wp_proof, log.Logs.Add.wp_proof, log.Logs.Merge.wp_proof⟩

end results

end Perennial.github_com.tangledbytes.go_vsr.pkg
