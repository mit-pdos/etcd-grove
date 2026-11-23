/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/events/Results.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension.
-/
/-
The results of `events`: one theorem per spec of `Spec/events.lean`, over the `encoding/json`
hypotheses (`Proof/events/LibHyps.lean`) and the kit's codec hypothesis `vsrnet.codecOk`
(`Spec/json.lean`), taken as arguments. Not here:
* `events.newDecoder.spec` and `events.Decoder.Decode_frame.spec`: the hub states them as
  hypotheses (`json.NewDecoder`, `Decoder.Decode` of the model's opaque decoder; the lab proved
  them of its own, `jsonstream`); `Decode_frame.spec` is an argument of `vsrwire`'s results;
* `events.initialize'.spec`: gone from the hub (the generated `pkg/events/Init.lean` proves the
  package's initialization; the lab's `Proof/events/Init.lean` is not ported);
* the lab's `Wrap.lean` (`Decode_frame` from its decoder's proof): nothing to wrap.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.events.SetFrameDecoder
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.events.ToWriter
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.events.FromDecoder

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section newNetworkEvent
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : events.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [π : NetProtoGS] [encoding.json.DecoderRep GF]
variable [encoding.json.Assumptions] [C : models_lab.jsoncodec.JsonCodec GF]

set_option goose.wp.extras true in
theorem events.NewNetworkEvent.wp : events.NewNetworkEvent.spec (GF := GF) (hG := hG) := by
  intro src ev
  wp_start
  wp_auto
  iapply HΦ
  itrivial

end newNetworkEvent

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : events.Assumptions] [log.Assumptions] [examples.vsrwire.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [π : NetProtoGS] [encoding.json.DecoderRep GF]
variable [encoding.json.Assumptions] [C : models_lab.jsoncodec.JsonCodec GF]
variable [encoding.json.EncoderRep GF]

theorem events.Event.ToWriter.wp
    (wp_NewEncoder : encoding.json.NewEncoder.spec (GF := GF) (hG := hG))
    (wp_Encode : encoding.json.Encoder.Encode_conn.kitSpec (GF := GF) (hG := hG)
      (jc := examples.vsrnet.jsonCodec))
    (codec_ok : examples.vsrnet.codecOk (GF := GF) (hG := hG)) :
    events.Event.ToWriter.spec (GF := GF) (hG := hG) :=
  events.Event.ToWriter.wp' wp_NewEncoder wp_Encode codec_ok

theorem events.Event.FromDecoder.wp
    (wp_Decode_frame : events.Decoder.Decode_frame.spec (GF := GF) (hG := hG))
    (wp_Unmarshal : encoding.json.Unmarshal.kitSpec (GF := GF) (hG := hG)
      (jc := examples.vsrnet.jsonCodec))
    (codec_ok : examples.vsrnet.codecOk (GF := GF) (hG := hG)) :
    events.Event.FromDecoder.spec (GF := GF) (hG := hG) :=
  events.Event.FromDecoder.wp' wp_Decode_frame wp_Unmarshal codec_ok

theorem events.SetFrameDecoder.wp : events.SetFrameDecoder.spec (GF := GF) (hG := hG) :=
  events.SetFrameDecoder.wp'

end results

end Perennial.github_com.tangledbytes.go_vsr.pkg
