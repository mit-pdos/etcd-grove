/-
**The vr kit's `encoding/json` interface** (notes/dsv-vr.md, "The JSON interface"): every premise
the kit's proof takes about `encoding/json` and the kit's (not yet generated) JSON codec, in one
place, so that it can be swapped for the main tree's specs when they land (zeldovich's J1,
`prove-ps2-jsonlean`, and the codec jsongen will write, `ps2-jsongen`). Nothing else in the kit's
proof states a JSON premise; the machines' proofs take these as arguments and `Link.lean` passes
`JsonHyps`' fields.

* Data (no instance anywhere; universally quantified at the statement): the model's `*Decoder`
  and `*Encoder` representations, `encoding.json.DecoderRep GF` (`Spec/jsonlib.lean`) and
  `encoding.json.EncoderRep GF` (`Proof/events/LibHyps.lean`). J1: the same two classes,
  `Proof/encoding/json/Registry.lean`.
* `JsonHyps` (a `Prop`), its fields:
  - `Unmarshal`, `NewEncoder`, `Encode_conn`: `encoding.json.{Unmarshal, NewEncoder,
    Encoder.Encode_conn}.spec` (`Proof/events/LibHyps.lean`). J1 states these three
    (`Spec/encoding/json/Codec/*`), with `codecSet ∗ kitCodecOk F` generalized to
    `codecSetWith fm fu ∗ codecOkWith F fm fu`, at `fm`/`fu` = our `kitFn`s.
  - `newDecoder`, `Decode_frame`: `pkg.events.{newDecoder, Decoder.Decode_frame}.spec`
    (`Spec/events.lean`): `json.NewDecoder` over a connection and `Decoder.Decode` of a
    `vsrwire.Frame`, stated at go-vsr's stream (`events.rstream` over `DecoderRep`). J1 has no
    `NewDecoder`/`Decode` spec yet.
  - `codecOk`: `vsrnet.codecOk` (`Spec/json.lean`): the kit's generated codec functions
    (`jsonMarshal`, `jsonUnmarshal`, jsongen's) meet the kit's `JsonCodec`, `jsoncodec.Scan`
    computes `scanF`. Neither branch gives it: it is the proof of jsongen's output for the kit's
    types (the lab's ~8k lines, `VsrProof/Proof/vsrnetjson`), which needs `log.Logs`'
    `MarshalJSON`/`UnmarshalJSON` specs (jsongen's `jenc_`/`jdec_` call them).
  - `RegisterJSON`: `vsrnet.RegisterJSON.codecSet_spec` (below): the kit's `RegisterJSON()` leaves
    the codec registered (`codecSet`). **Not true of today's placeholder** (`register_goose.go`:
    an empty body, since jsongen refused `log.Logs`); it is the spec of jsongen's
    `RegisterJSON` (`SetCodec(&json.Codec{jsonMarshal, jsonUnmarshal, jsoncodec.Scan})`), which
    needs `SetCodec`'s spec (J2's bodies; J1 keeps the model's bodies opaque).
* Not here (a separate premise of the statement): `encoding.json.InitHyp` (the names-only
  package's initializer; J1 proves `wp_initialize'` with no axiom, so it goes away with J1).
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

/-- **JSON premise** (see the file header): the kit's `RegisterJSON()` registers its codec. False of
today's placeholder (an empty body); jsongen's registration's spec. -/
abbrev RegisterJSON.codecSet_spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet }}
    (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.RegisterJSON)) (Val #()))
  {{ RET #(); encoding.json.codecSet (GF := GF) }}

/-- **The kit's JSON premises**, one `Prop` (see the file header). -/
structure JsonHyps : Prop where
  Unmarshal : encoding.json.Unmarshal.spec (GF := GF) (hG := hG)
    (jc := examples.vsrnet.jsonCodec)
  NewEncoder : encoding.json.NewEncoder.spec (GF := GF) (hG := hG)
  Encode_conn : encoding.json.Encoder.Encode_conn.spec (GF := GF) (hG := hG)
    (jc := examples.vsrnet.jsonCodec)
  newDecoder : pkg.events.newDecoder.spec (GF := GF) (hG := hG)
  Decode_frame : pkg.events.Decoder.Decode_frame.spec (GF := GF) (hG := hG)
  codecOk : examples.vsrnet.codecOk (GF := GF) (hG := hG)
  RegisterJSON : RegisterJSON.codecSet_spec (GF := GF) (hG := hG)

end hyps

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
