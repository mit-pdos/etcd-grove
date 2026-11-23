/-
What the replica's handler proofs take as hypotheses, bundled (`replica.Hyps`, one theorem argument
`H` instead of six): the `log/slog` logger methods' specs (`LibHyps.lean`: no `log/slog` model
here), and the specs of the two calls into sibling packages whose proofs are not ported yet,
`network.TCP.Send.spec` and `events.Event.ToWriter.spec` (the lab's `network.TCP.Send.wp`,
`events.Event.ToWriter.wp`, from `VsrProof/Proof/{network,events}/Results.lean`): both at every
JSON codec (the replica's codec is the one its `repInv` holds). `Results.lean` takes each as a
separate argument `(wp_X : X.spec)` and builds the bundle.

The bundle also carries the specs of the callees in the leaf packages `assert`, `ipv4port`,
`queue`, `time` and `log` (their proofs are in `Proof/<pkg>/`; the handlers see them through
their specs only, as the import tiers ask, CLAUDE.md "Import tiers"): `Results.lean` passes
their proofs.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.replica
public import Dsverify.Spec.log.slog.Logger
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.assert
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.ipv4port
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.queue
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.time
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.log

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

section hyps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

/-- The replica proof's hypotheses (the file header). -/
structure replica.Hyps : Prop where
  wp_Debug : log.slog.Logger.Debug.spec (GF := GF) (hG := hG)
  wp_Info : log.slog.Logger.Info.spec (GF := GF) (hG := hG)
  wp_Warn : log.slog.Logger.Warn.spec (GF := GF) (hG := hG)
  wp_Error : log.slog.Logger.Error.spec (GF := GF) (hG := hG)
  wp_TCP_Send : ∀ [jc : models_lab.jsoncodec.JsonCodec GF], network.TCP.Send.spec (GF := GF) (hG := hG)
  wp_ToWriter : ∀ [jc : models_lab.jsoncodec.JsonCodec GF],
    events.Event.ToWriter.spec (GF := GF) (hG := hG)
  wp_Assert : assert.Assert.spec (GF := GF) (hG := hG)
  wp_String : ipv4port.IPv4Port.String.spec (GF := GF) (hG := hG)
  wp_String_ptr : ipv4port.IPv4Port.String_ptr.spec (GF := GF) (hG := hG)
  wp_Push : queue.Queue.Push.spec (GF := GF) (hG := hG)
  wp_Pop : queue.Queue.Pop.spec (GF := GF) (hG := hG)
  wp_NewTimer : time.NewTimer.spec (GF := GF) (hG := hG)
  wp_Reset : time.Timer.Reset.spec (GF := GF) (hG := hG)
  wp_Done : time.Timer.Done.spec (GF := GF) (hG := hG)
  wp_SetState : time.Timer.SetState.spec (GF := GF) (hG := hG)
  wp_State : time.Timer.State.spec (GF := GF) (hG := hG)
  wp_Len : log.Logs.Len.spec (GF := GF) (hG := hG)
  wp_OpAt : log.Logs.OpAt.spec (GF := GF) (hG := hG)
  wp_ClientIDAt : log.Logs.ClientIDAt.spec (GF := GF) (hG := hG)
  wp_RequestIDAt : log.Logs.RequestIDAt.spec (GF := GF) (hG := hG)
  wp_After : log.Logs.After.spec (GF := GF) (hG := hG)
  wp_Add : log.Logs.Add.spec (GF := GF) (hG := hG)
  wp_Merge : log.Logs.Merge.spec (GF := GF) (hG := hG)

end hyps

end Perennial.github_com.tangledbytes.go_vsr.pkg
