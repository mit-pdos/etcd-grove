/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/client/Results.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension. The callees' specs of other vr packages
(`network.TCP.Send`, `events.Event.ToWriter`) and the `log/slog` hypotheses (`Logger.Error`,
`Logger.Debug`, `Dsverify/Spec/log/slog/Logger.lean`) are arguments.
-/
/-
The results of `client`: one theorem per spec of `Spec/client.lean`.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.client
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.client.CheckResult
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.client.Request
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.client.Submit
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.client.Run
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.client.New
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.ipv4port.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.queue.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.time.Results

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : client.Assumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]
variable [models_lab.jsoncodec.JsonCodec GF]
variable [network.Assumptions] [events.Assumptions] [net.Assumptions] [encoding.json.Assumptions]
variable [time.Assumptions] [queue.Assumptions] [log.slog.Assumptions] [ipv4port.Assumptions]
variable [sort.Assumptions]

theorem client.New.wp : client.New.spec (GF := GF) (hG := hG) :=
  client.New.wp_proof ipv4port.IPv4Port.FromHostPort.wp ipv4port.ByLess.sorter.wp queue.New.wp
theorem client.Client.Request.wp
    (wp_TCP_Send : network.TCP.Send.spec (GF := GF) (hG := hG))
    (wp_ToWriter : ∀ _jc : models_lab.jsoncodec.JsonCodec GF,
      events.Event.ToWriter.spec (GF := GF) (hG := hG)) :
    client.Client.Request.spec (GF := GF) (hG := hG) :=
  client.Client.Request.wp_proof wp_TCP_Send wp_ToWriter time.NewTimer.wp
theorem client.Client.Submit.wp
    (wp_Logger_Error : log.slog.Logger.Error.spec (GF := GF) (hG := hG)) :
    client.Client.Submit.spec (GF := GF) (hG := hG) :=
  client.Client.Submit.wp_proof wp_Logger_Error queue.Queue.Push.wp
theorem client.Client.Run.wp
    (wp_TCP_Send : network.TCP.Send.spec (GF := GF) (hG := hG))
    (wp_ToWriter : ∀ _jc : models_lab.jsoncodec.JsonCodec GF,
      events.Event.ToWriter.spec (GF := GF) (hG := hG))
    (wp_Logger_Error : log.slog.Logger.Error.spec (GF := GF) (hG := hG))
    (wp_Logger_Debug : log.slog.Logger.Debug.spec (GF := GF) (hG := hG)) :
    client.Client.Run.spec (GF := GF) (hG := hG) :=
  client.Client.Run.wp_proof wp_TCP_Send wp_ToWriter wp_Logger_Error wp_Logger_Debug
    queue.Queue.Pop.wp time.Timer.Done.wp time.Timer.Reset.wp
theorem client.Client.CheckResult.wp : client.Client.CheckResult.spec (GF := GF) (hG := hG) :=
  client.Client.CheckResult.wp_proof

end results

end Perennial.github_com.tangledbytes.go_vsr.pkg
