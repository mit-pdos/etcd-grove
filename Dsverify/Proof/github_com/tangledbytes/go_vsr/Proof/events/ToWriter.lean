/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/events/ToWriter.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension. What changed: `NewEncoder` and `Encode` are
the main tree's statements `encoding.json.NewEncoder.spec`, `encoding.json.Encoder.Encode_conn.spec`
(proved at the model's encoder, `encRepModel`: `Link.lean` passes them), the latter by the dispatch `marshalVia` (#24 J3: the
event's own `JSONModelMarshalPtr`), and the kit's JSON facts are `vsrnet.codecOk` (`Spec/json.lean`;
the lab's theorem `codec_ok`), at the kit's contract `vsrnet.jsonCodec`.
-/
/-
`ev.ToWriter(w)`: `json.NewEncoder(w).Encode(ev)` over the connection's writer (`wstream`), with
the kit's codec (`vsrnet.codecOk`, `vsrnet.enc_event`): the event's line is written whole, or
the write failed. The given codec and scanner (`kitCodecOk F`) are not needed.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.events
public import Spec.encoding.json.Codec.NewEncoder
public import Spec.encoding.json.Codec.Unmarshal
public import Spec.encoding.json.Codec.Encoder__Encode_conn
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.json

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem jsonstream_lines_snoc' (ms : List Msg) (m : Msg) :
    VsrWire.lines ms ++ (VsrWire.encEvent m ++ [W8 10]) = VsrWire.lines (ms ++ [m]) := by
  simp [VsrWire.lines, VsrWire.line]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : events.Assumptions] [log.Assumptions] [examples.vsrwire.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [π : NetProtoGS] [encoding.json.DecoderRep GF]
variable [encoding.json.Assumptions] [C : models_lab.jsoncodec.JsonCodec GF]
variable [encoding.json.EncoderRep GF]

set_option goose.wp.extras true

/-- `events.Event.ToWriter.spec`, for any codec instance `C` (unused: the kit's is used), over
`NewEncoder.spec`, `Encoder.Encode_conn.spec` (the main tree's) and `vsrnet.codecOk`. -/
theorem events.Event.ToWriter.wp'
    (wp_NewEncoder : encoding.json.NewEncoder.spec (GF := GF) (hG := hG))
    (wp_Encode : encoding.json.Encoder.Encode_conn.spec (GF := GF) (hG := hG))
    (codec_ok : examples.vsrnet.codecOk (GF := GF) (hG := hG)) :
    events.Event.ToWriter.spec (GF := GF) (hG := hG) := by
  intro F γ ev m w
  wp_start as ⟨#Hset, -, #Hev, #Hfact, %Hm, %Hmb, %Hml, Hw⟩
  unfold examples.vsrnet.codecOk at codec_ok
  ihave #Hok := codec_ok
  unfold events.wstream
  simp only [↓reduceIte]
  icases Hw with ⟨%cn, %s, %a, %W, #Hc, #Hnet, Htok, %ms, %HW, %Hpl, Hfacts⟩
  wp_auto
  wp_apply wp_NewEncoder w as %enc Henc
  ihave Hdep := examples.vsrnet.enc_event ev m Hm $$ [Hset Hev]
  · iframe; isplit
    · iPkgInit
    · iframe Hset; iexact Hev
  icases Hfacts with #Hfacts
  ihave #Hvia := encoding.json.kitCodecOk_marshalVia (jc := examples.vsrnet.jsonCodec)
    examples.vsrnet.scanF events.Event.ty ev (by simp [encoding.json.kitTypes]) (by go_type_set)
    $$ Hok
  wp_apply wp_Encode examples.vsrnet.jsonCodec examples.vsrnet.scanF enc _ w cn s a
    (VsrWire.protoOf γ) W _ $$ [Henc Htok Hdep] as %err Hpost
  · iframe
    isplitr
    · iexact Hvia
    isplitr
    · iexact Hc
    iintro %bs %hbs
    isplitl []
    · imodintro
      unfold VsrWire.protoOf
      iexists ms ++ [m]
      isplitr
      · ipureintro; rw [HW, Option.some.inj hbs, jsonstream_lines_snoc']; exact List.prefix_refl _
      isplitr
      · ipureintro; intro x hx; simp at hx; rcases hx with hx | hx
        · exact Hpl x hx
        · subst hx; exact ⟨Hm, Hmb, Hml⟩
      iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
      isplitl
      · iexact Hfacts
      · iexact Hfact
    · ipureintro; exact hbs
  icases Hpost with (⟨-, -, %Hnone⟩ | ⟨%bs, %k, %Hk, Htok, %hbs, #HerrOk⟩)
  · exact absurd Hnone (by simp)
  have hbs' := Option.some.inj hbs
  subst hbs'
  -- the error check
  cases err with
  | ok e =>
    wp_auto
    iapply HΦ
    iframe HerrOk
    rw [decide_eq_false (by simp)]
    iexists cn, s, a, _
    iframe Htok Hnet
    isplitr
    · iexact Hc
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  | nil =>
    wp_auto
    iapply HΦ
    iframe HerrOk
    rw [decide_eq_true rfl]
    have hk := Hk.2 rfl
    subst hk
    rw [List.take_of_length_le (by simp)]
    iexists cn, s, a, _
    iframe Htok Hnet
    isplitr
    · iexact Hc
    simp only [↓reduceIte]
    iexists ms ++ [m]
    isplitr
    · ipureintro; rw [HW, jsonstream_lines_snoc']
    isplitr
    · ipureintro; intro x hx; simp at hx; rcases hx with hx | hx
      · exact Hpl x hx
      · subst hx; exact ⟨Hm, Hmb, Hml⟩
    iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
    isplitl
    · iexact Hfacts
    · iexact Hfact

end proof

end Perennial.github_com.tangledbytes.go_vsr.pkg
