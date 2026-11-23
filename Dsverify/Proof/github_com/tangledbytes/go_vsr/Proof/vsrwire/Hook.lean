/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/vsrwire/Hook.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension. What changed: `dec.Decode(&f)` is the hub's
hypothesis `events.Decoder.Decode_frame.spec` (the lab proved it of its model's decoder,
`jsonstream.wp_Decode_frame`), taken as an argument; it asks for the codec (`codecSet`,
`kitCodecOk F`), which the frame decoder's precondition gives.
-/
/-
The G1 hook: `decodeFrame` is a frame decoder (`events.frameDecOk`); `vsrwire`'s `init` sets the
hook to it (`events.SetFrameDecoder`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.vsrwire
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.events.SetFrameDecoder

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [pkg.events.Assumptions] [examples.vsrwire.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [π : NetProtoGS] [encoding.json.DecoderRep GF]
variable [encoding.json.Assumptions] [C : models_lab.jsoncodec.JsonCodec GF]

set_option goose.wp.extras true

/-- `vsrwire.decodeFrame.spec`, over the hypothesis `Decoder.Decode_frame.spec`. -/
theorem examples.vsrwire.decodeFrame.wp'
    (wp_Decode_frame : pkg.events.Decoder.Decode_frame.spec (GF := GF) (hG := hG)) :
    isPkgInit (PROP := IProp GF) pkg_id.encoding.json ⊢
      pkg.events.frameDecOk (functions examples.vsrwire.decodeFrame []) := by
  iintro #Hpkg
  unfold pkg.events.frameDecOk
  imodintro
  iintro %F %γ %dec %Φ
  imodintro
  iintro ⟨#Hset, #HokF, Hrs⟩ HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_Decode_frame F γ dec f_ptr (zero_val examples.vsrwire.Frame) rfl $$ [Hrs f]
    as %err Hpost
  · iframe; isplit
    · iexact Hset
    · iexact HokF
  icases Hpost with ⟨Hrs, Hpost⟩
  cases err with
  | ok e =>
    rw [decide_eq_false (by simp)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hpost with ⟨%fr', Hf, #HerrOk⟩
    wp_auto
    iapply HΦ
    rw [decide_eq_false (by simp)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
    iexact HerrOk
  | nil =>
    simp only [_root_.decide_true, ↓reduceIte]
    icases Hpost with ⟨%m, %data, Hf, Hdata, %hm, %hmb, #Hfact⟩
    wp_auto
    iapply HΦ
    simp only [_root_.decide_true, ↓reduceIte]
    iframe Hrs
    iexists m
    iframe
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact hm
    isplitr
    · ipureintro; exact hmb
    iexact Hfact

theorem examples.vsrwire.decodeFrame_ne_nil :
    functions examples.vsrwire.decodeFrame [] ≠ func.nil := by
  intro h
  have e := (FuncUnfold.func_unfold (f := examples.vsrwire.decodeFrame) (type_args := []))
  rw [h, go.intoVal_unfold GoFunc] at e
  simp [func.nil, examples.vsrwire.decodeFrame.impl] at e

/-- `vsrwire.init0.spec`, over the hypothesis `Decoder.Decode_frame.spec`. -/
theorem examples.vsrwire.init0.wp'
    (wp_Decode_frame : pkg.events.Decoder.Decode_frame.spec (GF := GF) (hG := hG)) :
    examples.vsrwire.init0.spec (GF := GF) (hG := hG) := by
  wp_start as #Hk
  ihave #Hjson : isPkgInit (PROP := IProp GF) pkg_id.encoding.json $$ []
  · iPkgInit
  ihave #Hdf := examples.vsrwire.decodeFrame.wp' wp_Decode_frame $$ Hjson
  wp_apply pkg.events.SetFrameDecoder.wp' (functions examples.vsrwire.decodeFrame [])
    examples.vsrwire.decodeFrame_ne_nil $$ [] as #Hset
  · iframe; isplit
    · iexact Hk
    · iexact Hdf
  iapply HΦ $$ Hset

end proof

end Perennial.github_com.tangledbytes.go_vsr
