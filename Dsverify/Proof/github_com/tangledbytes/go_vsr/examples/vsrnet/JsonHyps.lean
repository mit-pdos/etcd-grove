/-
**The vr kit's `encoding/json` `Decoder` specs** (notes/dsv-vr.md, "The JSON interface"): the two
`Decoder` specs the machines' proofs take as arguments, in one `Prop`, over the `*Decoder`
representation `encoding.json.DecoderRep GF` (`Proof/encoding/json/Registry.lean`):
* `JsonHyps` (a `Prop`), its fields `newDecoder`, `Decode_frame` (`pkg.events.{newDecoder,
  Decoder.Decode_frame}.spec`, `Spec/events.lean`): `json.NewDecoder` over a connection and
  `Decoder.Decode` of a `vsrwire.Frame` (over the dispatch `unmarshalVia` at the frame), stated at
  go-vsr's stream (`events.rstream`).
Not premises: both hold at the model's decoder (`encoding.json.decRepModel`, over the model's
fields): `Link.lean`'s `jsonHypsModel`, from `Proof/events/DecodeFrame.lean`. The `*Encoder`'s
representation is the model's own (`encoding.json.encRepModel`), `NewEncoder` and `Encoder.Encode`
on a connection proved at it; `Unmarshal`, `SetCodec`, `RegisterJSON()` (`KitLib.lean`, from the
boot's `codecFresh`), the registered codec (`vsrnet.registeredCodecOk`) with `jsoncodec.Scan`'s
`scanOk`, and the kit's named types' own `JSONModel*` methods (`vsrnet.TypeMethods`) are proved
too; `codecOk` below takes the last three from `Link.lean`.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.json
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrnetjson.Vacuous
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.events
public import Spec.encoding.json.Codec.Unmarshal

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

attribute [local instance] Perennial.github_com.tangledbytes.go_vsr.examples.vsrnet.jsonCodec

section hyps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

/-- **The kit's JSON premises**, one `Prop` (see the file header). -/
structure JsonHyps : Prop where
  newDecoder : pkg.events.newDecoder.spec (GF := GF) (hG := hG)
  Decode_frame : pkg.events.Decoder.Decode_frame.spec (GF := GF) (hG := hG)

/-- The kit's JSON facts (`vsrnet.codecOk`: what the proofs take), from the premises. -/
theorem JsonHyps.codecOk (j : JsonHyps (GF := GF) (hG := hG))
    (hc : examples.vsrnet.registeredCodecOk (GF := GF) (hG := hG))
    (hs : ⊢ models_lab.jsoncodec.scanOk (GF := GF) examples.vsrnet.scanF
      models_lab.jsoncodec.scanFn)
    (hu : examples.vsrnet.TypeMethods (GF := GF) (hG := hG)) :
    examples.vsrnet.codecOk (GF := GF) (hG := hG) :=
  examples.vsrnet.codecOk_of hc hs hu

end hyps

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
