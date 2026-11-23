/-
The `encoding/json` library specs the `events` proofs take as **hypotheses** (notes/dsv-vr.md,
"Hypotheses": the model's `encoding/json` is translated names only here, so its functions have no
bodies to prove them from). Each is a `Prop`, taken as a theorem argument named after the lab's
spec (lab master 915f964, `Harness/Proof/encoding/json/{Valid,Stream}.lean`,
`VsrProof/Proof/jsonstream/Encode.lean`); none is assumed (no axiom, no instance). The vocabulary is
`Spec/jsonlib.lean`'s, plus `EncoderRep` (below).

* `encoding.json.Unmarshal.spec`: the lab's, unchanged (`Valid.lean`).
* `encoding.json.NewEncoder.spec`: the lab's (`Stream.lean`), the encoder's representation a class
  (`EncoderRep.encOk`, as `DecoderRep` for the decoder: the model's `Encoder` is opaque here) in
  place of the lab model's fields (`ownEncoder enc w nil`).
* `encoding.json.Encoder.Encode_conn.spec`: `enc.Encode(v)` on a fresh encoder writing to a
  connection end (`net.isConn`, `sendTok`), the lab's `jsonstream.wp_Encode_conn` (which the lab
  proved from its model's `Encode` and `TCPConn.Write`): the encoding and a newline are written in
  one `Write` (`k` bytes of them; all when the error is `nil`), or `Marshal` failed (nothing
  written). Stated over the connection, as the hub's decoder hypotheses (`events.newDecoder.spec`,
  `events.Decoder.Decode_frame.spec`) are, rather than over a generic writer contract: the lab's
  generic `Encoder.Encode.spec` asks the writer for `errOrNil` errors, which a connection's write
  `*OpError` does not have a spec for here (no `OpError.Error` spec in `Net/`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.events

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net

attribute [local instance] GooseGlobalGS.gooseInvGS

namespace encoding.json

/-- The representation of the model's `*Encoder` (opaque here; no instance is given):
`encOk enc w`, a healthy encoder (no sticky error) writing to `w`. -/
class EncoderRep [GooseExts] (GF : BundledGFunctors) where
  encOk : Loc → GoInterface → IProp GF

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [encoding.json.Assumptions] [jc : models_lab.jsoncodec.JsonCodec GF]

set_option goose.wp.extras true

/-- **Hypothesis** (the lab's `Unmarshal.spec`): `Unmarshal(data, ptr)`: on valid JSON
(`jsonValid F`), the kit's `jsonUnmarshal` (`JsonCodec.dec`; `err` is nil exactly when it
decoded); else a syntax error (non-nil), with nothing decoded. -/
abbrev Unmarshal.spec : Prop :=
  ∀ (F : List w8 → Bool → w64 × w64) (data : GoSlice) (dq : DFrac) (bs : List w8)
    (ptr : GoInterface) (Ψ : Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗ codecSet (GF := GF) ∗
      kitCodecOk F ∗ data ↦*{dq} bs ∗ models_lab.jsoncodec.JsonCodec.dec bs ptr Ψ }}
    (App (App (Val (@! encoding.json.Unmarshal)) (Val #data)) (Val #ptr))
  {{ (err : GoInterface), RET #err; data ↦*{dq} bs ∗
      ((⌜models_lab.jsoncodec.jsonValid F bs⌝ ∗ ∃ ok, ⌜err = interface.nil ↔ ok = true⌝ ∗ Ψ ok) ∨
       (⌜¬ models_lab.jsoncodec.jsonValid F bs ∧ err ≠ interface.nil⌝ ∗
         models_lab.jsoncodec.JsonCodec.dec bs ptr Ψ)) }}

variable [EncoderRep GF]

/-- **Hypothesis** (the lab's `NewEncoder.spec`): `NewEncoder(w)`: an encoder writing to `w`,
with no error. -/
abbrev NewEncoder.spec : Prop :=
  ∀ (w : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json }}
    (App (Val (@! encoding.json.NewEncoder)) (Val #w))
  {{ (enc : Loc), RET #enc; EncoderRep.encOk (GF := GF) enc w }}

variable [HasExt netExt] [net.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

/-- **Hypothesis** (the lab's `jsonstream.wp_Encode_conn`): `enc.Encode(v)`, `enc` a healthy
encoder writing to the end `s` of a connection `cn` (`net.isConn`) whose written stream (protocol
`P`) is `W`, the encoding allowed after `W`: `Marshal` failed (`err` non-nil, `Ψ none`, nothing
written); or the encoding `bs` and a newline were written in one `Write`, `k` bytes of them (all of
them when `err` is nil), `err` some error or nil. -/
abbrev Encoder.Encode_conn.spec : Prop :=
  ∀ (F : List w8 → Bool → w64 × w64) (enc : Loc) (v w : GoInterface) (cn : Nat) (s : Bool)
    (a : GoString) (P : Proto GF) (W : List w8) (Ψ : Option (List w8) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.json ∗
      codecSet (GF := GF) ∗ kitCodecOk F ∗ EncoderRep.encOk (GF := GF) enc w ∗
      net.isConn w cn s a ∗ sendTok cn s P W ∗ models_lab.jsoncodec.JsonCodec.enc v Ψ ∗
      (∀ bs, Ψ (some bs) -∗ □ P cn (W ++ (bs ++ [W8 10])) ∗ Ψ (some bs)) }}
    (App (Val (enc @!! go.GoType.PointerType encoding.json.Encoder.ty @!! go!"Encode")) (Val #v))
  {{ (err : GoInterface), RET #err;
      (⌜err ≠ interface.nil⌝ ∗ sendTok cn s P W ∗ Ψ none) ∨
      (∃ (bs : List w8) (k : Nat),
        ⌜k ≤ bs.length + 1 ∧ (err = interface.nil → k = bs.length + 1)⌝ ∗
        sendTok cn s P (W ++ (bs ++ [W8 10]).take k) ∗ Ψ (some bs) ∗
        bufio.errOrNil err) }}

end spec

end encoding.json
end Perennial
