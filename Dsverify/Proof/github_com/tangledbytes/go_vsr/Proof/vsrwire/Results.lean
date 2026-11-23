/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/vsrwire/Results.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension.
-/
/-
The results of `vsrwire`: one theorem per spec of `Spec/vsrwire.lean`, `decodeFrame`'s over the hub's
hypothesis `events.Decoder.Decode_frame.spec` (`dec.Decode(&f)` of the model's opaque decoder),
taken as an argument; `init0`'s over none.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.vsrwire
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrwire.Hook

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : vsrwire.Assumptions] [pkg.events.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [π : NetProtoGS] [encoding.json.DecoderRep GF]
variable [encoding.json.Assumptions] [C : models_lab.jsoncodec.JsonCodec GF]

theorem vsrwire.decodeFrame.wp
    (wp_Decode_frame : pkg.events.Decoder.Decode_frame.spec (GF := GF) (hG := hG)) :
    vsrwire.decodeFrame.spec (GF := GF) (hG := hG) :=
  examples.vsrwire.decodeFrame.wp' wp_Decode_frame

theorem vsrwire.init0.wp : vsrwire.init0.spec (GF := GF) (hG := hG) :=
  examples.vsrwire.init0.wp'

end results

end Perennial.github_com.tangledbytes.go_vsr.examples
