/-
What the replica's handler proofs take as hypotheses, bundled (`replica.Hyps`, one theorem argument
`H` instead of six): the `log/slog` logger methods' specs (`LibHyps.lean`: no `log/slog` model
here), and the specs of the two calls into sibling packages whose proofs are not ported yet,
`network.TCP.Send.spec` and `events.Event.ToWriter.spec` (the lab's `network.TCP.Send.wp`,
`events.Event.ToWriter.wp`, from `VsrProof/Proof/{network,events}/Results.lean`): both at every
JSON codec (the replica's codec is the one its `repInv` holds). `Results.lean` takes each as a
separate argument `(wp_X : X.spec)` and builds the bundle.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.replica
public import Dsverify.Spec.log.slog.Logger

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

end hyps

end Perennial.github_com.tangledbytes.go_vsr.pkg
