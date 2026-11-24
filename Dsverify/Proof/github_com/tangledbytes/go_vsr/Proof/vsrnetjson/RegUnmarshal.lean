/-
The registered codec's `Unmarshal` (`examples/vsrnet/json_gen.go`'s `jsonUnmarshal`, jsongen's)
meets `codecPart vsrnet.jsonCodec` (`unmarshalOk`): of `decP`'s three cases the codec gets only
the `*[]log.Log` one (`unmarshalsByCodec`: `*vsrwire.Frame` and the payloads `*events.<T>` have
`JSONModelUnmarshal`, so the dispatch never sends them to the codec), which `jdec_S_log_Log`
decodes (`SLogDec.lean`). Over the specs of `jsoncodec`'s decoding helpers (section hypotheses).
Ported from dsverify-lab's `examples/vr/proof/VsrProof/Proof/vsrnetjson/{UnmarshalAll,CodecOk}.lean`
(`wp_jsonUnmarshal_logs`, `vsrnet.unmarshalOk_proof`'s `[]Log` case; lab master 915f964).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrnetjson.SLogDec

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- Every payload type's pointer has `JSONModelUnmarshal` (jsongen's same-package methods). -/
theorem vsrnet.payload_unmarshaler [GooseExts] [GooseSemantics] [GooseInterp]
    [go_gctx : GoGlobalContext] [vsrnet.Assumptions] (m : Msg) :
    go.typeSetContains (go.GoType.PointerType (pkg.events.payloadTy m))
      encoding.json.modelUnmarshaler.ty = true := by
  cases m <;> simp only [pkg.events.payloadTy] <;> go_type_set

/-- `*vsrwire.Frame` has `JSONModelUnmarshal`. -/
theorem vsrnet.frame_unmarshaler [GooseExts] [GooseSemantics] [GooseInterp]
    [go_gctx : GoGlobalContext] [vsrnet.Assumptions] :
    go.typeSetContains (go.GoType.PointerType vsrwire.Frame.ty)
      encoding.json.modelUnmarshaler.ty = true := by
  go_type_set

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [vsrnet.Assumptions]
variable (wp_At : models_lab.jsoncodec.At.spec (GF := GF) (hG := hG))
variable (wp_Empty : models_lab.jsoncodec.Empty.spec (GF := GF) (hG := hG))
variable (wp_Member : models_lab.jsoncodec.Member.spec (GF := GF) (hG := hG))
variable (wp_Next : models_lab.jsoncodec.Next.spec (GF := GF) (hG := hG))
variable (wp_String : models_lab.jsoncodec.String.spec (GF := GF) (hG := hG))
variable (wp_QuotedUint : models_lab.jsoncodec.QuotedUint.spec (GF := GF) (hG := hG))

set_option goose.wp.extras true

include wp_At wp_Empty wp_Member wp_Next wp_String wp_QuotedUint in
/-- `jsonUnmarshal(data, p)`, `p` a `*[]log.Log` holding nil, on a `[]Log`'s encoding. -/
theorem vsrnet.wp_jsonUnmarshal_logs (data : GoSlice) (dq : DFrac) (bs : List w8) (p : Loc)
    (es : List Entry) (hes : ∀ e ∈ es, e.cid < 2 ^ 64 ∧ e.req < 2 ^ 64 ∧ PlainStr e.op)
    (hb : bs = VsrJson.ser (VsrJson.logsJV es)) :
    {{ (data ↦*{dq} bs ∗ p ↦ (slice.nil : GoSlice) : IProp GF) }}
      (App (App (Val (@! vsrnet.jsonUnmarshal)) (Val #data))
        (Val #(interface.mkOk (go.GoType.PointerType (go.GoType.SliceType pkg.log.Log.ty)) #p)))
    {{ RET #(interface.nil : GoInterface); data ↦*{dq} bs ∗
        ∃ sl : GoSlice, p ↦ sl ∗ pkg.log.ownLogs sl (DFrac.own 1) es ∗
          ownSliceCap pkg.log.Log sl (DFrac.own 1) }} := by
  wp_start as ⟨Hs, Hp⟩
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_auto
  try rw [decide_eq_false Hpnn]
  try wp_auto
  wp_apply (vsrnet.wp_jdec_S_log_Log wp_At wp_Empty wp_Member wp_Next wp_String wp_QuotedUint
    data dq bs (W64 0) p err_ptr es [] hes (by simp [hb])) $$ [Hs Hp] as ⟨Hs, %sl, Hp, Hl, Hcap⟩
  · iframe
  try wp_auto
  iapply HΦ
  iframe

include wp_At wp_Empty wp_Member wp_Next wp_String wp_QuotedUint in
/-- **The registered codec's `Unmarshal` meets `codecPart vsrnet.jsonCodec`.** -/
theorem vsrnet.registeredUnmarshalOk :
    ⊢ (letI : models_lab.jsoncodec.JsonCodec GF :=
        encoding.json.codecPart (vsrnet.jsonCodec (GF := GF))
       models_lab.jsoncodec.unmarshalOk (GF := GF) vsrnet.scanF
         (encoding.json.kitFn go!"jsonUnmarshal")) := by
  unfold models_lab.jsoncodec.unmarshalOk
  rw [show encoding.json.kitFn go!"jsonUnmarshal" = functions vsrnet.jsonUnmarshal [] from rfl]
  imodintro
  iintro %data %dq %bs %ptr %Ψ %Φ %hv Hs Hdec HΦ
  simp only [encoding.json.codecPart]
  icases Hdec with ⟨%hby, Hdec⟩
  rw [vsrnet.dec_eq]
  unfold vsrnet.decP
  icases Hdec with (⟨%_, %ws, %m, %p, %fr, %hb, %hws, %hm, %hfr, %hptr, Hp, Hk⟩ |
    ⟨%_, %_, %_, %m, %p, %hb, %hm, %hmb, %hptr, Hpkg, Hset, Hz, Hk⟩ |
    ⟨%_, %es, %p, %hb, %hes, %hptr, Hp, Hk⟩)
  · subst hptr
    simp only [encoding.json.unmarshalsByCodec, interface.mkOk, vsrnet.frame_unmarshaler] at hby
    cases hby
  · subst hptr
    simp only [encoding.json.unmarshalsByCodec, interface.mkOk, vsrnet.payload_unmarshaler] at hby
    cases hby
  · subst hptr
    wp_apply (vsrnet.wp_jsonUnmarshal_logs wp_At wp_Empty wp_Member wp_Next wp_String wp_QuotedUint
      data dq bs p es hes (by rw [hb]; rfl)) $$ [Hs Hp] as ⟨Hs, %sl, Hp, Hl, Hcap⟩
    · iframe
    iapply HΦ $$ %_ %true Hs
    · ipureintro; simp
    iapply Hk
    iframe

end proof

end Perennial.github_com.tangledbytes.go_vsr.examples
