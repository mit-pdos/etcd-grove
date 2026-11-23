/-
**The vr kit's `encoding/json` interface** (notes/dsv-vr.md, "The JSON interface", "JSON on the
main tree"): every premise the kit's proof takes about `encoding/json` and the kit's JSON codec, in
one place. Nothing else in the kit's proof states a JSON premise; the machines' proofs take these as
arguments and `Link.lean` passes `JsonHyps`' fields. The package `encoding/json` is the main tree's
(the model, J1/J2 of mit-pdos/etcd-grove#24; its initializer is proved).

* Data (no instance anywhere; universally quantified at the statement): the model's `*Decoder`
  and `*Encoder` representations, the main tree's `encoding.json.DecoderRep GF` and
  `encoding.json.EncoderRep GF` (`Proof/encoding/json/Registry.lean`).
* `JsonHyps` (a `Prop`), its fields:
  - `Unmarshal`, `Encode_conn`: `encoding.json.{Unmarshal, Encoder.Encode_conn}.kitSpec`
    (`Proof/events/LibHyps.lean`): the lab's, at the kit's registered codec (`codecSet ∗
    kitCodecOk F`). The main tree's `Unmarshal.spec` (proved, J2) and `Encoder.Encode_conn.spec`
    take `unmarshalVia`/`marshalVia` instead, whose codec route is `codecSetWith` (with the
    registry's mutex) and whose per-type route is the type's own methods, for every contract `J`;
    moving onto them changes these premises other than by removal (notes/dsv-vr.md).
  - `NewEncoder`: the main tree's `encoding.json.NewEncoder.spec`
    (`Spec/encoding/json/Codec/NewEncoder.lean`), the same statement as vr's was.
  - `newDecoder`, `Decode_frame`: `pkg.events.{newDecoder, Decoder.Decode_frame}.spec`
    (`Spec/events.lean`): `json.NewDecoder` over a connection and `Decoder.Decode` of a
    `vsrwire.Frame`, stated at go-vsr's stream (`events.rstream` over `DecoderRep`). The main tree
    has no `NewDecoder`/`Decode` spec yet.
  - `codecOk`: `vsrnet.codecOk` (`Spec/json.lean`): the kit's generated codec functions
    (`jsonMarshal`, `jsonUnmarshal`, jsongen's) meet the kit's `JsonCodec`, `jsoncodec.Scan`
    computes `scanF`: the proof of jsongen's output for the kit's types (the lab's ~8k lines).
  - `RegisterJSON`: `vsrnet.RegisterJSON.codecSet_spec` (below): the kit's `RegisterJSON()` leaves
    the codec registered (`codecSet`). **Not true of today's code**: its precondition does not
    exclude a codec already registered (then `SetCodec` panics); the main tree's `SetCodec.spec`
    needs `codecUnset` and the registry's mutex from the deployment's boot.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.json
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.events.LibHyps

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

/-- **JSON premise** (see the file header): the kit's `RegisterJSON()` registers its codec. False
of the code (jsongen's `SetCodec(&json.Codec{jsonMarshal, jsonUnmarshal, jsoncodec.Scan})`): the
precondition does not exclude a codec already registered, and then `SetCodec` panics; the main
tree's `SetCodec.spec` takes `codecUnset` and the registry's mutex, a boot resource. -/
abbrev RegisterJSON.codecSet_spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet }}
    (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.RegisterJSON)) (Val #()))
  {{ RET #(); encoding.json.codecSet (GF := GF) }}

/-- **The kit's JSON premises**, one `Prop` (see the file header). -/
structure JsonHyps : Prop where
  Unmarshal : encoding.json.Unmarshal.kitSpec (GF := GF) (hG := hG)
    (jc := examples.vsrnet.jsonCodec)
  NewEncoder : encoding.json.NewEncoder.spec (GF := GF) (hG := hG)
  Encode_conn : encoding.json.Encoder.Encode_conn.kitSpec (GF := GF) (hG := hG)
    (jc := examples.vsrnet.jsonCodec)
  newDecoder : pkg.events.newDecoder.spec (GF := GF) (hG := hG)
  Decode_frame : pkg.events.Decoder.Decode_frame.spec (GF := GF) (hG := hG)
  codecOk : examples.vsrnet.codecOk (GF := GF) (hG := hG)
  RegisterJSON : RegisterJSON.codecSet_spec (GF := GF) (hG := hG)

end hyps

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
