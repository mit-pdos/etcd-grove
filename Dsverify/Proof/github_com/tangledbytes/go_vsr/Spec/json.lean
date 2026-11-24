/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Spec/json.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension. What changed: there is no generated codec yet (jsongen refuses
go-vsr's `log.Logs`, notes/dsv-vr.md finding 2), so the lab's theorem `vsrnet.codec_ok` (the
generated functions meet the codec, proved in the lab's `Proof/vsrnetjson`) is here the
**hypothesis statement** `vsrnet.codecOk` (a `Prop`, to be taken by the kit's theorems until the
codec's proof exists); the codec `vsrnet.jsonCodec` is a `def` (a local instance here; the lab's was a
global instance); the JSON vocabulary is `models_lab.jsoncodec`'s. The facts are the lab's, proved
the same way (from the codec's definition and the Lean scanner), `encoding.json.Assumptions`
in place of the lab's package state.
-/
/-
The kit's JSON codec (`examples/vsrnet/json_*gen.go`, registered with the `encoding/json`
model by `registerJSON`) as the specs see it: the `JsonCodec GF` instance (`enc`, `dec`,
the JSON prover's choice) and its scanner `scanF` (what `jsoncodec.Scan` computes), with
`codec_ok : ⊢ kitCodecOk scanF` (the codec's functions meet them).

The specs of `log` (`MarshalJSON`, `UnmarshalJSON`) and `events` (`ToWriter`, `FromDecoder`)
take `JsonCodec GF` as a parameter and the scanner as an argument; this file fixes them.
The facts the `log` and `events` proofs need of the codec (below): an event's encoding is
`VsrWire.encEvent m`; the scanner frames a line (`scanF_line`, `scanF_partial`); a line decodes
into a `vsrwire.Frame` with `m`'s type and payload bytes, and the payload bytes into `m`'s
payload; a `Logs`' encoding is `encLogs` and decodes back. They need the strings to be plain
(`VsrModel.PlainStr`, `VsrModel.PlainMsg`): the codec panics on others.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.events
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.jsoncodec.Valid
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.jsoncodec.Codec

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- JSON whitespace, both ways. -/
theorem vsrnet.isSpaceB_spB (c : w8) : encoding.json.isSpaceB c = JsonScan.spB c := by
  simp [encoding.json.isSpaceB, JsonScan.spB]

/-- The kit's scanner (`jsoncodec.Scan`'s function: `(op, end)` of a prefix of the input).
-- sealed: the JSON prover's choice -/
def vsrnet.scanF : List w8 → Bool → w64 × w64 := JsonScan.scanF

section codec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- The kit's codec: `enc v Ψ` the deposit for `Marshal(v)`, `dec bs ptr Ψ` the deposit for
`Unmarshal(bs, ptr)`.
-- sealed: the JSON prover's choice -/
def vsrnet.jsonCodec : models_lab.jsoncodec.JsonCodec GF := vsrnet.codecInst

attribute [local instance] vsrnet.jsonCodec

theorem vsrnet.enc_eq : @models_lab.jsoncodec.JsonCodec.enc _ _ (vsrnet.jsonCodec (GF := GF)) =
    vsrnet.encP := rfl
theorem vsrnet.dec_eq : @models_lab.jsoncodec.JsonCodec.dec _ _ (vsrnet.jsonCodec (GF := GF)) =
    vsrnet.decP := rfl

end codec

section premises
attribute [local instance] vsrnet.jsonCodec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [encoding.json.Assumptions]

/-- **Premise** (#24 J3; the lab's theorem `codec_ok`, for the registered codec's share): the kit's
registered codec (`examples/vsrnet/json_gen.go`'s `jsonMarshal`, `jsonUnmarshal`, jsongen's for
the unnamed roots `[]log.Log` and the frame struct) meets `codecPart vsrnet.jsonCodec`
(`marshalOk`, `unmarshalOk`). The third part of the main tree's `codecOkWith`, `scanOk scanF scanFn`
(`jsoncodec.Scan` computes `scanF`), is proved (`Net/Proof/models_lab/jsoncodec/ScanOk.lean`,
linked in `examples/vsrnet/Link.lean`), so no longer part of this premise.

True of the code: `codecPart` keeps only the values the dispatch sends to the codec, whose types
have no `JSONModel*` method. Of `encP`'s cases that leaves the `[]log.Log` (the `*events.Event`
case has `JSONModelMarshalPtr`), of `decP`'s the `*[]log.Log` (`*vsrwire.Frame` and the payloads
`*events.<T>` have `JSONModelUnmarshal`); `jsonMarshal` encodes a `[]log.Log` of plain operations
as encoding/json does, which is `log.encLogs es` (jsongen's generated test `json_gen_test.go`
compares the codec with real encoding/json; `encLogs` is the lab's proved encoding of the same
values), and `jsonUnmarshal` decodes `encLogs es` (ids below `2^64`, plain operations) into a
nil `*[]log.Log` as a fresh slice of `es`. -/
def vsrnet.registeredCodecOk : Prop :=
  ⊢ (letI := encoding.json.codecPart (vsrnet.jsonCodec (GF := GF))
     iprop(models_lab.jsoncodec.marshalOk (encoding.json.kitFn go!"jsonMarshal") ∗
       models_lab.jsoncodec.unmarshalOk vsrnet.scanF (encoding.json.kitFn go!"jsonUnmarshal")))

/-- **Premise** (#24 J3): the substantive part of the main tree's `typeCodecOk vsrnet.jsonCodec
scanF T` for the kit's types (`encoding.json.kitTypes`), one field per method/type pair where the
kit's contract gives a deposit: `(*events.Event).JSONModelMarshalPtr`, and `JSONModelUnmarshal` of
each payload type and of `vsrwire.Frame`. Every other part of `typeCodecOk` (a value type's
`JSONModelMarshal`, the other types' `JSONModelMarshalPtr`, `*Event`'s `JSONModelUnmarshal`, all of
`log.Logs`) holds because `jsonCodec` gives no deposit there, and is proved
(`Proof/vsrnetjson/Vacuous.lean`: `vsrnet.codecOk_of`).

True of the code (jsongen's same-package methods): `marshalAt`/`unmarshalAt` constrain a method
only at `J`'s deposits. `event`: on a `*events.Event` of a message with plain strings
(`encP`), `JSONModelMarshalPtr` encodes, never failing, `VsrWire.encEvent m`: `jenc_Event`
writes `{"@type":N,"data":…}`, the payload by `jencAny`, a `Logs` by its `MarshalJSON`, i.e.
`json.Marshal([]Log)` through the registered codec, which `encP`'s `codecSet` registers and
`registeredCodecOk` covers; this is real encoding/json's output (jsongen's same-package tests,
`json_model_gen_test.go`, run by `jsonmodel_forks.py`, compare the methods with it), which
`encEvent` is. `frame`: on whitespace and a line's value `encEvent m` into a `Frame` with a nil
`Data` (`decP`), `JSONModelUnmarshal` (valid, so it decodes) gives `Frame{typeOf m, data}`, `data`
a fresh slice of the raw payload `encPayload m`. The payloads: on `encPayload m` into a zero
payload (`decP`; numbers below `2^64`, `MsgBound`), the payload `m`'s, a `Logs` through its
`UnmarshalJSON`, i.e. the registered codec. -/
structure vsrnet.TypeCodecs : Prop where
  event : ∀ l : Loc, ⊢ encoding.json.marshalAt (vsrnet.jsonCodec (GF := GF))
    #(methods (go.GoType.PointerType pkg.events.Event.ty) go!"JSONModelMarshalPtr" #l)
    (interface.mkOk (go.GoType.PointerType pkg.events.Event.ty) #l)
  request : ∀ l : Loc, ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
    #(methods (go.GoType.PointerType pkg.events.Request.ty) go!"JSONModelUnmarshal" #l)
    (interface.mkOk (go.GoType.PointerType pkg.events.Request.ty) #l)
  reply : ∀ l : Loc, ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
    #(methods (go.GoType.PointerType pkg.events.Reply.ty) go!"JSONModelUnmarshal" #l)
    (interface.mkOk (go.GoType.PointerType pkg.events.Reply.ty) #l)
  prepare : ∀ l : Loc, ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
    #(methods (go.GoType.PointerType pkg.events.Prepare.ty) go!"JSONModelUnmarshal" #l)
    (interface.mkOk (go.GoType.PointerType pkg.events.Prepare.ty) #l)
  prepareOK : ∀ l : Loc, ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
    #(methods (go.GoType.PointerType pkg.events.PrepareOK.ty) go!"JSONModelUnmarshal" #l)
    (interface.mkOk (go.GoType.PointerType pkg.events.PrepareOK.ty) #l)
  commit : ∀ l : Loc, ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
    #(methods (go.GoType.PointerType pkg.events.Commit.ty) go!"JSONModelUnmarshal" #l)
    (interface.mkOk (go.GoType.PointerType pkg.events.Commit.ty) #l)
  startViewChange : ∀ l : Loc, ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
    #(methods (go.GoType.PointerType pkg.events.StartViewChange.ty) go!"JSONModelUnmarshal" #l)
    (interface.mkOk (go.GoType.PointerType pkg.events.StartViewChange.ty) #l)
  doViewChange : ∀ l : Loc, ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
    #(methods (go.GoType.PointerType pkg.events.DoViewChange.ty) go!"JSONModelUnmarshal" #l)
    (interface.mkOk (go.GoType.PointerType pkg.events.DoViewChange.ty) #l)
  startView : ∀ l : Loc, ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
    #(methods (go.GoType.PointerType pkg.events.StartView.ty) go!"JSONModelUnmarshal" #l)
    (interface.mkOk (go.GoType.PointerType pkg.events.StartView.ty) #l)
  getState : ∀ l : Loc, ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
    #(methods (go.GoType.PointerType pkg.events.GetState.ty) go!"JSONModelUnmarshal" #l)
    (interface.mkOk (go.GoType.PointerType pkg.events.GetState.ty) #l)
  newState : ∀ l : Loc, ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
    #(methods (go.GoType.PointerType pkg.events.NewState.ty) go!"JSONModelUnmarshal" #l)
    (interface.mkOk (go.GoType.PointerType pkg.events.NewState.ty) #l)
  heartbeat : ∀ l : Loc, ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
    #(methods (go.GoType.PointerType pkg.events.Heartbeat.ty) go!"JSONModelUnmarshal" #l)
    (interface.mkOk (go.GoType.PointerType pkg.events.Heartbeat.ty) #l)
  frame : ∀ l : Loc, ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
    #(methods (go.GoType.PointerType vsrwire.Frame.ty) go!"JSONModelUnmarshal" #l)
    (interface.mkOk (go.GoType.PointerType vsrwire.Frame.ty) #l)

/-- The kit's JSON facts at the kit's codec and scanner (what the proofs take; the lab's theorem
`codec_ok`), from the two premises: `vsrnet.codecOk_of` (`Proof/vsrnetjson/Vacuous.lean`). -/
def vsrnet.codecOk : Prop := ⊢ encoding.json.kitCodecOk (GF := GF) vsrnet.scanF

end premises

section facts
attribute [local instance] vsrnet.jsonCodec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [encoding.json.Assumptions]
variable [pkg.log.Assumptions] [pkg.events.Assumptions] [vsrwire.Assumptions]

open VsrModel pkg

/-- An event of a message with plain strings is encoded (never an error) as `encEvent m`. -/
theorem vsrnet.enc_event (ev : Loc) (m : Msg) (hm : PlainMsg m) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
      encoding.json.codecSet (GF := GF) ∗ events.isEvent ev m ⊢
    models_lab.jsoncodec.JsonCodec.enc (interface.mkOk (go.GoType.PointerType events.Event.ty) #ev)
      (fun r => iprop(⌜r = some (VsrWire.encEvent m)⌝)) := by
  iintro ⟨#Hpkg, #Hset, #Hev⟩
  rw [vsrnet.enc_eq]; unfold vsrnet.encP
  ileft
  iexists ‹pkg.log.Assumptions›, ‹pkg.events.Assumptions›, ‹encoding.json.Assumptions›, ev, m
  simp only []
  isplitr; · ipureintro; trivial
  isplitr; · ipureintro; exact hm
  isplitr; · iexact Hpkg
  isplitr; · iexact Hset
  isplitr; · iexact Hev
  ipureintro; trivial

/-- The scanner finds a line's value, after whitespace, whatever follows it. -/
theorem vsrnet.scanF_line (ws : List w8) (m : Msg) (rest : List w8) (eof : Bool)
    (hws : ∀ c ∈ ws, encoding.json.isSpaceB c = true) (hm : PlainMsg m) :
    vsrnet.scanF (ws ++ VsrWire.encEvent m ++ rest) eof =
      (W64 0, W64 (ws.length + (VsrWire.encEvent m).length)) := by
  have hsp : ∀ c ∈ ws, JsonScan.spB c = true := fun c hc => by
    rw [← vsrnet.isSpaceB_spB]; exact hws c hc
  simp only [vsrnet.scanF, JsonScan.scanF, VsrWire.encEvent, VsrJson.scanL_line ws m rest eof hsp hm]
  push_cast; rfl

/-- The scanner asks for more on whitespace followed by a strict prefix of an encoding (not at
the end of the stream). -/
theorem vsrnet.scanF_partial (ws pre : List w8) (m : Msg)
    (hws : ∀ c ∈ ws, encoding.json.isSpaceB c = true) (hm : PlainMsg m)
    (hpre : pre <+: VsrWire.encEvent m) (hne : pre ≠ VsrWire.encEvent m) :
    (vsrnet.scanF (ws ++ pre) false).1 = W64 1 := by
  have hsp : ∀ c ∈ ws, JsonScan.spB c = true := fun c hc => by
    rw [← vsrnet.isSpaceB_spB]; exact hws c hc
  simp only [vsrnet.scanF, JsonScan.scanF, VsrJson.scanL_partial false ws pre m hsp hm hpre hne]
  rfl

/-- An encoding after whitespace is valid JSON (below 2^64 bytes: `jsonValid` reads the end as a
`w64`; codec-6, D5). -/
theorem vsrnet.encEvent_valid (ws : List w8) (m : Msg)
    (hws : ∀ c ∈ ws, encoding.json.isSpaceB c = true) (hm : PlainMsg m)
    (hlen : (ws ++ VsrWire.encEvent m).length < 2 ^ 64) :
    models_lab.jsoncodec.jsonValid vsrnet.scanF (ws ++ VsrWire.encEvent m) := by
  simp only [VsrWire.encEvent, VsrJson.encEvent_plain m hm] at hlen ⊢
  exact VsrJson.valid_value ws _ (VsrJson.evJV_ok m hm) (VsrJson.evJV_maxd m)
    (by simp [VsrJson.evJV, VsrJson.termOK]) hws hlen

/-- A line's value (after whitespace) decodes into a `vsrwire.Frame` with a nil `Data`
(`decodeFrame`'s `Frame{}`; codec-3, D5) holding `m`'s type and its payload's bytes (a fresh
slice). -/
theorem vsrnet.dec_frame (ws : List w8) (m : Msg) (p : Loc) (fr : vsrwire.Frame)
    (hws : ∀ c ∈ ws, encoding.json.isSpaceB c = true) (hm : PlainMsg m)
    (hfr : fr.Data' = slice.nil) :
    (p ↦ fr : IProp GF) ⊢
    models_lab.jsoncodec.JsonCodec.dec (ws ++ VsrWire.encEvent m)
      (interface.mkOk (go.GoType.PointerType vsrwire.Frame.ty) #p)
      (fun ok => iprop(⌜ok = true⌝ ∗ ∃ data : GoSlice,
        p ↦ vsrwire.Frame.mk (events.typeOf m) data ∗ data ↦* events.encPayload m ∗
        ownSliceCap w8 data (DFrac.own 1))) := by
  iintro Hp
  rw [vsrnet.dec_eq]; unfold vsrnet.decP
  ileft
  iexists ‹vsrwire.Assumptions›, ws, m, p, fr
  simp only []
  isplitr; · ipureintro; trivial
  isplitr; · ipureintro; exact hws
  isplitr; · ipureintro; exact hm
  isplitr; · ipureintro; exact hfr
  isplitr; · ipureintro; trivial
  isplitl [Hp]; · iexact Hp
  iintro %data H
  isplitr
  · ipureintro; trivial
  iexists data
  iexact H

/-- A payload's bytes are valid JSON (below 2^64 bytes; codec-6, D5). -/
theorem vsrnet.encPayload_valid (m : Msg) (hm : PlainMsg m)
    (hlen : (events.encPayload m).length < 2 ^ 64) :
    models_lab.jsoncodec.jsonValid vsrnet.scanF (events.encPayload m) := by
  obtain ⟨ms, hms⟩ := VsrJson.payJV_obj m
  have := VsrJson.valid_value [] (VsrJson.payJV m) (VsrJson.payJV_ok m hm)
    (VsrJson.payJV_maxd m) (by rw [hms]; trivial) (by simp) hlen
  simpa [vsrnet.scanF, events.encPayload, log.encLogs, VsrJson.encPayload, VsrJson.encLogs] using this

/-- A payload's bytes decode into a zero value of its type: the payload (its `Logs` fresh), its
numbers in `uint64` (`MsgBound`: the decoder rejects larger ones; codec-1, D5). -/
theorem vsrnet.dec_payload (m : Msg) (p : Loc) (hm : PlainMsg m) (hb : MsgBound m) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
      encoding.json.codecSet (GF := GF) ∗ events.payloadZero p m ⊢
    models_lab.jsoncodec.JsonCodec.dec (events.encPayload m)
      (interface.mkOk (go.GoType.PointerType (events.payloadTy m)) #p)
      (fun ok => iprop(⌜ok = true⌝ ∗ events.payloadAt p m)) := by
  iintro ⟨#Hpkg, #Hset, Hz⟩
  rw [vsrnet.dec_eq]; unfold vsrnet.decP
  iright; ileft
  iexists ‹pkg.log.Assumptions›, ‹pkg.events.Assumptions›, ‹encoding.json.Assumptions›, m, p
  simp only []
  isplitr; · ipureintro; trivial
  isplitr; · ipureintro; exact hm
  isplitr; · ipureintro; exact hb
  isplitr; · ipureintro; trivial
  isplitr; · iexact Hpkg
  isplitr; · iexact Hset
  isplitl [Hz]; · iexact Hz
  iintro H
  isplitr; · ipureintro; trivial
  iexact H

/-- A `[]log.Log` holding entries with plain operations is encoded as `encLogs`. -/
theorem vsrnet.enc_logs (sl : GoSlice) (dq : DFrac) (es : List Entry)
    (hes : ∀ e ∈ es, PlainStr e.op) :
    log.ownLogs (GF := GF) sl dq es ⊢
    models_lab.jsoncodec.JsonCodec.enc (interface.mkOk (go.GoType.SliceType log.Log.ty) #sl)
      (fun r => iprop(⌜r = some (log.encLogs es)⌝ ∗ log.ownLogs sl dq es)) := by
  iintro Hl
  rw [vsrnet.enc_eq]; unfold vsrnet.encP
  iright
  iexists ‹pkg.log.Assumptions›, sl, dq, es
  simp only []
  isplitr; · ipureintro; trivial
  isplitr; · ipureintro; exact hes
  isplitl [Hl]; · iexact Hl
  iintro Hl
  isplitr; · ipureintro; trivial
  iexact Hl

/-- `encLogs` is valid JSON (below 2^64 bytes; codec-6, D5). -/
theorem vsrnet.encLogs_valid (es : List Entry) (hes : ∀ e ∈ es, PlainStr e.op)
    (hlen : (log.encLogs es).length < 2 ^ 64) :
    models_lab.jsoncodec.jsonValid vsrnet.scanF (log.encLogs es) := by
  have := VsrJson.valid_value [] (VsrJson.logsJV es) (VsrJson.logsJV_ok es hes)
    (VsrJson.logsJV_maxd es) trivial (by simp) hlen
  simpa [vsrnet.scanF, events.encPayload, log.encLogs, VsrJson.encPayload, VsrJson.encLogs] using this

/-- `encLogs es` decodes into a nil `[]log.Log` variable (the decoder panics on a non-nil one;
codec-4, D5): a fresh slice of `es` (its ids in `uint64`, its operations plain; codec-1, D5). -/
theorem vsrnet.dec_logs (es : List Entry) (p : Loc) (sl0 : GoSlice)
    (hes : ∀ e ∈ es, e.cid < 2 ^ 64 ∧ e.req < 2 ^ 64 ∧ PlainStr e.op)
    (hsl0 : sl0 = slice.nil) :
    (p ↦ sl0 : IProp GF) ⊢
    models_lab.jsoncodec.JsonCodec.dec (log.encLogs es)
      (interface.mkOk (go.GoType.PointerType (go.GoType.SliceType log.Log.ty)) #p)
      (fun ok => iprop(⌜ok = true⌝ ∗ ∃ sl : GoSlice, p ↦ sl ∗
        log.ownLogs sl (DFrac.own 1) es ∗ ownSliceCap log.Log sl (DFrac.own 1))) := by
  subst hsl0
  iintro Hp
  rw [vsrnet.dec_eq]; unfold vsrnet.decP
  iright; iright
  iexists ‹pkg.log.Assumptions›, es, p
  simp only []
  isplitr; · ipureintro; trivial
  isplitr; · ipureintro; exact hes
  isplitr; · ipureintro; trivial
  isplitl [Hp]; · iexact Hp
  iintro %sl H
  isplitr
  · ipureintro; trivial
  iexists sl
  iexact H

end facts

end Perennial.github_com.tangledbytes.go_vsr.examples
