/-
**The vr kit's `encoding/json` interface** (notes/dsv-vr.md, "The JSON interface", "JSON on the
main tree"): every premise the kit's proof takes about `encoding/json` and the kit's JSON codec, in
one place. Nothing else in the kit's proof states a JSON premise; the machines' proofs take these as
arguments and `Link.lean` passes `JsonHyps`' fields. The package `encoding/json` is the main tree's
(the model, J1/J2/J3 of mit-pdos/etcd-grove#24; its initializer is proved, and so is its first run
on a machine, which leaves the registry fresh: `BootLinked.lean`). Proved, not premises: the main
tree's `Unmarshal.spec` (`Unmarshal.wp`) and `SetCodec.spec` (`SetCodec.wp`), the kit's
`RegisterJSON()` (`KitLib.lean`, from the boot's `codecFresh`), and (round 8) the registered
codec, `vsrnet.registeredCodecOk` (`Proof/vsrnetjson/Registered.lean`) with `jsoncodec.Scan`'s
`scanOk` (`Net/Proof/models_lab/jsoncodec/ScanOk.lean`), which `codecOk` below takes from
`Link.lean`.

* Data (no instance anywhere; universally quantified at the statement): the model's `*Decoder`
  and `*Encoder` representations, the main tree's `encoding.json.DecoderRep GF` and
  `encoding.json.EncoderRep GF` (`Proof/encoding/json/Registry.lean`).
* `JsonHyps` (a `Prop`), its fields, each true of the code as it stands (the argument is each
  statement's docstring):
  - `NewEncoder`, `Encode_conn`: **the main tree's statements** `encoding.json.NewEncoder.spec`
    (`Spec/encoding/json/Codec/NewEncoder.lean`) and `encoding.json.Encoder.Encode_conn.spec`
    (`Spec/encoding/json/Codec/Encoder__Encode_conn.lean`: `enc.Encode(v)` on a connection, by the
    dispatch `marshalVia J F v`, for every contract `J`), not yet proved there (`EncoderRep` is
    still a class).
  - `newDecoder`, `Decode_frame`: `pkg.events.{newDecoder, Decoder.Decode_frame}.spec`
    (`Spec/events.lean`): `json.NewDecoder` over a connection and `Decoder.Decode` of a
    `vsrwire.Frame` (over the dispatch `unmarshalVia` at the frame), stated at go-vsr's stream
    (`events.rstream` over `DecoderRep`). The main tree has no `NewDecoder`/`Decode` spec yet.
  - `types`: `vsrnet.TypeCodecs` (`Spec/json.lean`): the kit's named types' own `JSONModel*`
    methods (jsongen's same-package mode) meet `vsrnet.jsonCodec` where it gives a deposit (13
    fields: `*Event`'s `JSONModelMarshalPtr`, the 11 payloads' and `Frame`'s
    `JSONModelUnmarshal`); the rest of the main tree's `typeCodecOk` for the 14 types (`log.Logs`
    whole) is proved (`Proof/vsrnetjson/Vacuous.lean`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.json
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrnetjson.Vacuous
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.events
public import Spec.encoding.json.Codec.NewEncoder
public import Spec.encoding.json.Codec.Unmarshal
public import Spec.encoding.json.Codec.Encoder__Encode_conn

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
variable [encoding.json.DecoderRep GF] [encoding.json.EncoderRep GF]

/-- **The kit's JSON premises**, one `Prop` (see the file header). -/
structure JsonHyps : Prop where
  NewEncoder : encoding.json.NewEncoder.spec (GF := GF) (hG := hG)
  Encode_conn : encoding.json.Encoder.Encode_conn.spec (GF := GF) (hG := hG)
  newDecoder : pkg.events.newDecoder.spec (GF := GF) (hG := hG)
  Decode_frame : pkg.events.Decoder.Decode_frame.spec (GF := GF) (hG := hG)
  types : examples.vsrnet.TypeCodecs (GF := GF) (hG := hG)

/-- The kit's JSON facts (`vsrnet.codecOk`: what the proofs take), from the premises. -/
theorem JsonHyps.codecOk (j : JsonHyps (GF := GF) (hG := hG))
    (hc : examples.vsrnet.registeredCodecOk (GF := GF) (hG := hG))
    (hs : ⊢ models_lab.jsoncodec.scanOk (GF := GF) examples.vsrnet.scanF
      models_lab.jsoncodec.scanFn) :
    examples.vsrnet.codecOk (GF := GF) (hG := hG) :=
  examples.vsrnet.codecOk_of hc hs j.types

end hyps

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
