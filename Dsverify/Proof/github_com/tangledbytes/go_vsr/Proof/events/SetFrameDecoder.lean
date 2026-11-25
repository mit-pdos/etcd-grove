/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/events/SetFrameDecoder.lean (lab master
915f964; notes/dsv-vr.md): the hub's `events.SetFrameDecoder.spec` is the package proof's
`pkg/events/SetFrameDecoder.lean` (`wp_SetFrameDecoder`, what `vsrwire`'s generated `Init.lean`
calls): the hook's lock is events' package fact.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.events
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.events.SetFrameDecoder

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : events.Assumptions] [examples.vsrwire.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [π : NetProtoGS] [encoding.json.DecoderRep GF]
variable [encoding.json.Assumptions] [models_lab.jsoncodec.JsonCodec GF]

theorem events.SetFrameDecoder.wp' : events.SetFrameDecoder.spec (GF := GF) (hG := hG) :=
  events.wp_SetFrameDecoder

end proof

end Perennial.github_com.tangledbytes.go_vsr.pkg
