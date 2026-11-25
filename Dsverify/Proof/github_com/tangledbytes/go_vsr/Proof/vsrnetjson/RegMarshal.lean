/-
The registered codec's `Marshal` (`examples/vsrnet/json_gen.go`'s `jsonMarshal`, jsongen's) meets
`codecPart vsrnet.jsonCodec` (`marshalOk`): of `encP`'s two cases the codec gets only the
`[]log.Log` one (`marshalsByCodec`: `*events.Event` has `JSONModelMarshalPtr`, so the dispatch
never sends it to the codec), which `jencAny` hands to `jenc_S_log_Log` (`LogEnc.lean`). Over the
specs of `jsoncodec`'s `AppendRaw`, `AppendQuotedUint`, `AppendString` (section hypotheses).
Ported from dsverify-lab's `examples/vr/proof/VsrProof/Proof/vsrnetjson/{MarshalTop,CodecOk}.lean`
(`wp_jsonMarshal_logs`, `vsrnet.marshalOk_proof`'s `[]Log` case; lab master 915f964).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrnetjson.LogEnc

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [vsrnet.Assumptions]
variable (wp_AppendRaw : models_lab.jsoncodec.AppendRaw.spec (GF := GF) (hG := hG))
variable (wp_AppendQuotedUint : models_lab.jsoncodec.AppendQuotedUint.spec (GF := GF) (hG := hG))
variable (wp_AppendString : models_lab.jsoncodec.AppendString.spec (GF := GF) (hG := hG))

/-- `*events.Event` has `JSONModelMarshalPtr` (jsongen's same-package methods). -/
theorem vsrnet.event_marshalerPtr :
    go.typeSetContains (go.GoType.PointerType pkg.events.Event.ty)
      encoding.json.modelMarshalerPtr.ty = true := by
  go_type_set

set_option goose.wp.extras true

include wp_AppendRaw wp_AppendQuotedUint wp_AppendString in
/-- `jsonMarshal(v)`, `v` a `[]log.Log` of entries with plain operations. -/
theorem vsrnet.wp_jsonMarshal_logs (sl : GoSlice) (dq : DFrac) (es : List Entry)
    (hes : ∀ e ∈ es, PlainStr e.op) :
    {{ (pkg.log.ownLogs sl dq es : IProp GF) }}
      (App (Val (@! vsrnet.jsonMarshal))
        (Val #(interface.mkOk (go.GoType.SliceType pkg.log.Log.ty) #sl)))
    {{ (s : GoSlice), RET (PairV #s #(interface.nil : GoInterface));
        s ↦* VsrJson.ser (VsrJson.logsJV es) ∗ ownSliceCap w8 s (DFrac.own 1) ∗
        pkg.log.ownLogs sl dq es }} := by
  wp_start as Hl
  wp_auto
  wp_apply wp_slice_make2 (V := w8) (W64 0) $$ [] as %b ⟨Hb, Hcap⟩
  · ipureintro; decide
  simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
  try wp_auto
  wp_func_call
  wp_call
  wp_auto
  wp_apply (vsrnet.wp_jenc_S_log_Log wp_AppendRaw wp_AppendQuotedUint wp_AppendString
    _ _ sl dq es (W64 0) (by decide) hes) $$ [$Hl $Hb $Hcap] as %b' ⟨Hb, Hcap, Hl⟩
  try wp_auto
  iapply HΦ
  simp only [List.nil_append]
  iframe

include wp_AppendRaw wp_AppendQuotedUint wp_AppendString in
/-- **The registered codec's `Marshal` meets `codecPart vsrnet.jsonCodec`.** -/
theorem vsrnet.registeredMarshalOk :
    ⊢ (letI : models_lab.jsoncodec.JsonCodec GF :=
        encoding.json.codecPart (vsrnet.jsonCodec (GF := GF))
       models_lab.jsoncodec.marshalOk (GF := GF) (encoding.json.kitFn go!"jsonMarshal")) := by
  have henc : ∀ (v : GoInterface) (Ψ : Option (List w8) → IProp GF),
      @models_lab.jsoncodec.JsonCodec.enc _ GF (encoding.json.codecPart (vsrnet.jsonCodec (GF := GF)))
        v Ψ = iprop(⌜encoding.json.marshalsByCodec v⌝ ∗ vsrnet.encP v Ψ) :=
    fun _ _ => rfl
  unfold models_lab.jsoncodec.marshalOk
  simp only [henc]
  rw [show encoding.json.kitFn go!"jsonMarshal" = functions vsrnet.jsonMarshal [] from rfl]
  imodintro
  iintro %v %Ψ %Φ ⟨%hby, Henc⟩ HΦ
  unfold vsrnet.encP
  icases Henc with (⟨%_, %_, %_, %ev, %m, %hv, %hm, Hpkg, Hset, Hev, HΨ⟩ |
    ⟨%_, %sl, %dq, %es, %hv, %hes, Hl, HΨ⟩)
  · subst hv
    simp only [encoding.json.marshalsByCodec, interface.mkOk, vsrnet.event_marshalerPtr] at hby
    exact absurd hby.1 (by decide)
  · subst hv
    iapply (vsrnet.wp_jsonMarshal_logs wp_AppendRaw wp_AppendQuotedUint wp_AppendString
      sl dq es hes) $$ [Hl]
    · iexact Hl
    inext
    iintro %s ⟨Hs, Hcap, Hl⟩
    icases HΦ with ⟨HΦ, -⟩
    rw [show VsrJson.ser (VsrJson.logsJV es) = pkg.log.encLogs es from rfl]
    iapply HΦ $$ Hs Hcap
    iapply HΨ $$ Hl

end proof

end Perennial.github_com.tangledbytes.go_vsr.examples
