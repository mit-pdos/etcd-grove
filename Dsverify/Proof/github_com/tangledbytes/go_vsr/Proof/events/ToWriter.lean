/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/events/ToWriter.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension. What changed: `NewEncoder` and `Encode` are
the hypotheses `encoding.json.NewEncoder.spec`, `encoding.json.Encoder.Encode_conn.spec`
(`Proof/events/LibHyps.lean`; the lab proved them of its model), and the kit's codec is the
hypothesis `vsrnet.codecOk` (`Spec/json.lean`; the lab's theorem `codec_ok`), all at the kit's
codec `vsrnet.jsonCodec`.
-/
/-
`ev.ToWriter(w)`: `json.NewEncoder(w).Encode(ev)` over the connection's writer (`wstream`), with
the kit's codec (`vsrnet.codecOk`, `vsrnet.enc_event`): the event's line is written whole, or
the write failed. The given codec and scanner (`kitCodecOk F`) are not needed.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.events.LibHyps
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
the hypotheses `NewEncoder.spec`, `Encoder.Encode_conn.spec` (at the kit's codec) and
`vsrnet.codecOk`. -/
theorem events.Event.ToWriter.wp'
    (wp_NewEncoder : encoding.json.NewEncoder.spec (GF := GF) (hG := hG))
    (wp_Encode : encoding.json.Encoder.Encode_conn.spec (GF := GF) (hG := hG)
      (jc := examples.vsrnet.jsonCodec))
    (codec_ok : examples.vsrnet.codecOk (GF := GF) (hG := hG)) :
    events.Event.ToWriter.spec (GF := GF) (hG := hG) := by
  intro F γ ev m w
  wp_start as ⟨#Hset, -, #Hev, #Hfact, %Hm, %Hmb, %Hml, Hw⟩
  unfold examples.vsrnet.codecOk at codec_ok
  ihave #Hok := codec_ok
  unfold events.wstream
  simp only [↓reduceIte]
  icases Hw with ⟨%cn, %s, %a, %W, #Hc, Htok, %ms, %HW, %Hpl, Hfacts⟩
  wp_auto
  wp_apply wp_NewEncoder w as %enc Henc
  ihave Hdep := examples.vsrnet.enc_event ev m Hm $$ [Hset Hev]
  · iframe; isplit
    · iPkgInit
    · iframe Hset; iexact Hev
  icases Hfacts with #Hfacts
  wp_apply wp_Encode examples.vsrnet.scanF enc _ w cn s a (VsrWire.protoOf γ) W _
    $$ [Henc Htok Hdep] as %err Hpost
  · iframe
    isplitr
    · iexact Hset
    isplitr
    · iexact Hok
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
    iframe Htok
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
    iframe Htok
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
