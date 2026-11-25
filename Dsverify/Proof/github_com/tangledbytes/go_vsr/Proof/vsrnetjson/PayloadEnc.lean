/-
`events.Event`'s generated encoder (`events`' `json_model_gen.go`, jsongen's same-package methods:
`(*Event).JSONModelMarshalPtr`, `jenc_Event`, `jencAny`, `jenc_<T>`, and for a `Logs` member
`jenc_p0_log_Logs` → `Logs.MarshalJSON` → `jencValue`) on an event of a message with plain strings:
it writes `VsrWire.encEvent m`. Over the specs of `jsoncodec`'s encoding helpers and
`log.Logs.MarshalJSON` (the bundle `vsrnet.EncSpecs`, linked in `examples/vsrnet/Link.lean`).
Ported from dsverify-lab's `examples/vr/proof/VsrProof/Proof/vsrnetjson/{EncFlat,EncLogs,Marshal}.lean`
(lab master 915f964): the depth arguments, the `Logs` members (`jencValue`: `Valid`, `Nesting`,
`AppendCompact`) and the top (`JSONModelMarshalPtr`) are new, round 9 (notes/dsv-vr.md).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrnetjson.PayloadDec
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrnetjson.LogEnc
public import Net.Spec.models_lab.jsoncodec.AppendCompact
public import Net.Spec.models_lab.jsoncodec.Nesting
public import Net.Spec.models_lab.jsoncodec.AppendUint
public import Net.Proof.models_lab.jsoncodec.Quote

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.iris.style.nameCheck false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## `AppendCompact` and `Nesting` on a `[]Log`'s encoding -/

theorem vsrnet.cmpRun_logJV (e : Entry) (h : PlainStr e.op) (rest : List w8) :
    models_lab.jsoncodec.cmpRun false (VsrJson.ser (VsrJson.logJV e) ++ rest) =
      models_lab.jsoncodec.cmpRun false rest := by
  have hop : ∀ c ∈ e.op, JsonScan.plainEnc c := h
  simp (config := { decide := true }) [VsrJson.ser, VsrJson.logJV, VsrJson.mkObj, VsrJson.serMs,
    VsrJson.serMsT, VsrJson.qn, models_lab.jsoncodec.cmpRun,
    models_lab.jsoncodec.cmpRun_body _ _ hop,
    models_lab.jsoncodec.cmpRun_body _ _ (models_lab.jsoncodec.decN_plainEnc _),
    JsonScan.spB, models_lab.jsoncodec.cmpBad]

theorem vsrnet.cmpRun_serVsT (es : List Entry) (h : ∀ e ∈ es, PlainStr e.op) (rest : List w8) :
    models_lab.jsoncodec.cmpRun false (VsrJson.serVsT (VsrJson.mkArr (es.map VsrJson.logJV)) ++ rest) =
      models_lab.jsoncodec.cmpRun false rest := by
  induction es with
  | nil => simp [VsrJson.serVsT, VsrJson.mkArr]
  | cons e es ih =>
    simp only [List.map_cons, VsrJson.mkArr, VsrJson.serVsT, List.cons_append, List.append_assoc]
    have h44 : JsonScan.spB VsrJson.cComma = false := by decide
    simp only [models_lab.jsoncodec.cmpRun, h44, Bool.false_eq_true, ↓reduceIte]
    rw [show decide (VsrJson.cComma = 34#8) = false by decide, vsrnet.cmpRun_logJV e (h e (by simp)),
      ih (fun e he => h e (by simp [he]))]

theorem vsrnet.cmpRun_logs (es : List Entry) (h : ∀ e ∈ es, PlainStr e.op) :
    models_lab.jsoncodec.cmpRun false (VsrJson.ser (VsrJson.logsJV es)) = some false := by
  have h91 : JsonScan.spB VsrJson.cLS = false := by decide
  cases es with
  | nil => simp (config := { decide := true }) [VsrJson.ser, VsrJson.logsJV, VsrJson.mkArr,
      VsrJson.serVs, models_lab.jsoncodec.cmpRun, JsonScan.spB]
  | cons e es =>
    simp only [VsrJson.ser, VsrJson.logsJV, List.map_cons, VsrJson.mkArr, VsrJson.serVs,
      List.cons_append, List.append_assoc]
    simp only [models_lab.jsoncodec.cmpRun, h91, Bool.false_eq_true, ↓reduceIte]
    rw [show decide (VsrJson.cLS = 34#8) = false by decide, vsrnet.cmpRun_logJV e (h e (by simp)),
      vsrnet.cmpRun_serVsT es (fun e he => h e (by simp [he]))]
    decide

theorem vsrnet.nestRun_logJV (e : Entry) (h : PlainStr e.op) (m : w64) (hm : m = 1 ∨ m = 2)
    (rest : List w8) :
    models_lab.jsoncodec.nestRun 1 m false (VsrJson.ser (VsrJson.logJV e) ++ rest) =
      models_lab.jsoncodec.nestRun 1 2 false rest := by
  have hop : ∀ c ∈ e.op, JsonScan.plainEnc c := h
  have hm2 : (if uint.Z ((1 : w64) + W64 1) > uint.Z m then (1 : w64) + W64 1 else m) = 2 := by
    rcases hm with rfl | rfl <;> decide
  simp only [VsrJson.ser, VsrJson.logJV, VsrJson.mkObj, VsrJson.serMs, VsrJson.serMsT, VsrJson.qn,
    List.cons_append, List.append_assoc, List.singleton_append, List.nil_append]
  simp (config := { decide := true }) only [models_lab.jsoncodec.nestRun, hm2, ↓reduceIte]
  simp (config := { decide := true }) [models_lab.jsoncodec.nestRun,
    models_lab.jsoncodec.nestRun_body _ _ _ _ hop,
    models_lab.jsoncodec.nestRun_body _ _ _ _ (models_lab.jsoncodec.decN_plainEnc _)]

theorem vsrnet.nestRun_serVsT (es : List Entry) (h : ∀ e ∈ es, PlainStr e.op) (rest : List w8) :
    models_lab.jsoncodec.nestRun 1 2 false
        (VsrJson.serVsT (VsrJson.mkArr (es.map VsrJson.logJV)) ++ rest) =
      models_lab.jsoncodec.nestRun 1 2 false rest := by
  induction es with
  | nil => simp [VsrJson.serVsT, VsrJson.mkArr]
  | cons e es ih =>
    simp only [List.map_cons, VsrJson.mkArr, VsrJson.serVsT, List.cons_append, List.append_assoc]
    simp (config := { decide := true }) only [models_lab.jsoncodec.nestRun, ↓reduceIte]
    rw [vsrnet.nestRun_logJV e (h e (by simp)) 2 (Or.inr rfl), ih (fun e he => h e (by simp [he]))]

/-- `Nesting` of a `[]Log`'s encoding: at most 2. -/
theorem vsrnet.nestRun_logs (es : List Entry) (h : ∀ e ∈ es, PlainStr e.op) :
    uint.nat (models_lab.jsoncodec.nestRun (W64 0) (W64 0) false (VsrJson.ser (VsrJson.logsJV es))) ≤ 2 := by
  cases es with
  | nil => simp (config := { decide := true }) [VsrJson.ser, VsrJson.logsJV, VsrJson.mkArr,
      VsrJson.serVs, models_lab.jsoncodec.nestRun]
  | cons e es =>
    simp only [VsrJson.ser, VsrJson.logsJV, List.map_cons, VsrJson.mkArr, VsrJson.serVs,
      List.cons_append, List.append_assoc]
    simp (config := { decide := true }) only [models_lab.jsoncodec.nestRun, ↓reduceIte]
    rw [show (W64 0 + W64 1 : w64) = 1 by decide,
      vsrnet.nestRun_logJV e (h e (by simp)) 1 (Or.inl rfl), vsrnet.nestRun_serVsT es (fun e he => h e (by simp [he]))]
    simp (config := { decide := true }) [models_lab.jsoncodec.nestRun]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [vsrnet.Assumptions]

/-- What the event encoder's proofs take: the specs of `jsoncodec`'s encoding helpers,
`log.Logs.MarshalJSON`'s, and the registered codec's facts (a `Logs` member's `MarshalJSON` goes
through `json.Marshal`'s codec route). All proved; `Link.lean` builds it. -/
structure vsrnet.EncSpecs : Prop where
  AppendRaw : models_lab.jsoncodec.AppendRaw.spec (GF := GF) (hG := hG)
  AppendUint : models_lab.jsoncodec.AppendUint.spec (GF := GF) (hG := hG)
  AppendQuotedUint : models_lab.jsoncodec.AppendQuotedUint.spec (GF := GF) (hG := hG)
  AppendString : models_lab.jsoncodec.AppendString.spec (GF := GF) (hG := hG)
  Valid : models_lab.jsoncodec.Valid.spec (GF := GF) (hG := hG)
  Nesting : models_lab.jsoncodec.Nesting.spec (GF := GF) (hG := hG)
  AppendCompact : models_lab.jsoncodec.AppendCompact.spec (GF := GF) (hG := hG)
  LogsMarshalJSON : pkg.log.Logs.MarshalJSON.spec (GF := GF) (hG := hG)

set_option goose.wp.extras true

/-- `jencValue(b, x, d)` on a value the codec wrote (valid, kept as it is by `AppendCompact`, not
nested too deep): `x` appended, no error. -/
theorem vsrnet.wp_jencValue (H : vsrnet.EncSpecs (GF := GF) (hG := hG)) (b : GoSlice)
    (bs : List w8) (x : GoSlice) (dq : DFrac) (rs : List w8) (d : w64)
    (hsc : JsonScan.scanL rs true = (0, rs.length))
    (hc : models_lab.jsoncodec.cmpRun false rs = some false) (hl : rs.getLast? ≠ some 92#8)
    (hn : uint.nat d + uint.nat (models_lab.jsoncodec.nestRun (W64 0) (W64 0) false rs) ≤ 10000) :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) ∗ x ↦*{dq} rs : IProp GF) }}
      (App (App (App (Val (@! pkg.events.jencValue)) (Val #b)) (Val #x)) (Val #d))
    {{ (b' : GoSlice), RET (PairV #b' #(interface.nil : GoInterface));
        b' ↦* (bs ++ rs) ∗ ownSliceCap w8 b' (DFrac.own 1) ∗ x ↦*{dq} rs }} := by
  wp_start as ⟨Hb, Hcap, Hx⟩
  wp_auto
  wp_apply (H.Valid x dq rs hsc) $$ Hx as Hx
  wp_apply (H.Nesting x dq rs hl) $$ Hx as Hx
  wp_if_destruct
  · exfalso; (try simp only [models_lab.jsoncodec.MaxDepth] at *); word
  try wp_auto
  wp_apply (H.AppendCompact b bs x dq rs hsc hc) $$ [$Hb $Hcap $Hx] as %b' ⟨Hb, Hcap, Hx⟩
  try wp_auto
  iapply HΦ
  iframe

/-- `jenc_p0_log_Logs(b, sl, d)` on a `Logs` holding plain entries: `l.MarshalJSON()` (the
registered codec's `encLogs`), then `jencValue`. -/
theorem vsrnet.wp_jenc_logs (H : vsrnet.EncSpecs (GF := GF) (hG := hG)) (b : GoSlice)
    (bs : List w8) (sl : GoSlice) (dq : DFrac) (es : List Entry) (d : w64)
    (hes : ∀ e ∈ es, PlainStr e.op) (hd : uint.nat d < 9500) :
    {{ (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
        vsrnet.logsRoute (GF := GF) ∗ pkg.log.ownLogs sl dq es ∗
        b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (App (Val (@! pkg.events.jenc_p0_log_Logs)) (Val #b)) (Val #sl)) (Val #d))
    {{ (b' : GoSlice), RET (PairV #b' #(interface.nil : GoInterface));
        b' ↦* (bs ++ VsrJson.ser (VsrJson.logsJV es)) ∗ ownSliceCap w8 b' (DFrac.own 1) ∗
        pkg.log.ownLogs sl dq es }} := by
  wp_start as ⟨#Hset, Hl, Hb, Hcap⟩
  wp_auto
  wp_method_call
  wp_auto
  have henc : pkg.log.ownLogs (GF := GF) sl dq es ⊢
      (encoding.json.codecPart (vsrnet.jsonCodec (GF := GF))).enc
        (interface.mkOk (go.GoType.SliceType pkg.log.Log.ty) #sl)
        (fun r => iprop(⌜r = some (pkg.log.encLogs es)⌝ ∗ pkg.log.ownLogs sl dq es)) := by
    rw [show ∀ (v : GoInterface) (Ψ : Option (List w8) → IProp GF),
        (encoding.json.codecPart (vsrnet.jsonCodec (GF := GF))).enc v Ψ =
        iprop(⌜encoding.json.marshalsByCodec v⌝ ∗ (vsrnet.jsonCodec (GF := GF)).enc v Ψ)
      from fun _ _ => rfl]
    iintro Hl
    isplitr
    · ipureintro; exact pkg.log.logs_marshalsByCodec sl
    iapply (vsrnet.enc_logs sl dq es hes)
    iexact Hl
  wp_apply (H.LogsMarshalJSON (encoding.json.codecPart (vsrnet.jsonCodec (GF := GF)))
    vsrnet.scanF sl dq es henc) $$ [Hl] as %raw ⟨Hl, Hraw, Hrcap⟩
  · iframe
    iexact Hset
  try wp_auto
  have hsc : JsonScan.scanL (pkg.log.encLogs es) true = (0, (pkg.log.encLogs es).length) := by
    have := VsrJson.top_v (VsrJson.logsJV es) (VsrJson.logsJV_ok es hes) [] 0 false true
      (VsrJson.logsJV_maxd es) trivial
    simpa [JsonScan.scanL, pkg.log.encLogs, VsrJson.encLogs] using this
  have hc : models_lab.jsoncodec.cmpRun false (pkg.log.encLogs es) = some false :=
    vsrnet.cmpRun_logs es hes
  have hn := vsrnet.nestRun_logs es hes
  have hl : (pkg.log.encLogs es).getLast? ≠ some 92#8 := by
    simp only [pkg.log.encLogs, VsrJson.encLogs, VsrJson.ser, VsrJson.logsJV]
    rw [List.getLast?_concat]
    decide
  wp_apply (vsrnet.wp_jencValue H b bs raw (DFrac.own 1) (pkg.log.encLogs es) d hsc hc hl
    (by simp only [pkg.log.encLogs, VsrJson.encLogs] at *; omega)) $$ [$Hb $Hcap $Hraw]
    as %b' ⟨Hb, Hcap, Hraw⟩
  try wp_auto
  iapply HΦ
  iframe

theorem vsrnet.wp_jenc_Request (H : vsrnet.EncSpecs (GF := GF) (hG := hG)) (b : GoSlice) (bs : List w8) (x : pkg.events.Request) (d : w64) (hd : uint.nat d < 9500)
    (hop : PlainStr x.Op') :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (App (Val (@! pkg.events.jenc_Request)) (Val #b)) (Val #x)) (Val #d))
    {{ (b' : GoSlice), RET (PairV #b' #(interface.nil : GoInterface));
        b' ↦* (bs ++ VsrJson.ser (VsrJson.payJV (.request (uint.nat x.ID') (uint.nat x.ClientID') x.Op'))) ∗
        ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_if_destruct
  · exfalso; (try simp only [models_lab.jsoncodec.MaxDepth] at *); word
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 123]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  repeat (first
    | wp_apply (H.AppendRaw _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (H.AppendQuotedUint _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | (wp_apply (H.AppendString _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
       rw [models_lab.jsoncodec.jsonQuote_plain _ (by assumption)])
    ; try wp_auto)
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 125]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  iapply HΦ
  simp only [VsrJson.ser, VsrJson.payJV, VsrJson.reqJV, VsrJson.mkObj, VsrJson.serMs,
    VsrJson.serMsT, VsrJson.qn, VsrJson.cQ, VsrJson.cColon, VsrJson.cComma, VsrJson.cLB,
    VsrJson.cRB, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
    show (W8 123 : w8) = 123#8 from rfl, show (W8 125 : w8) = 125#8 from rfl]
  iframe


theorem vsrnet.wp_jenc_Reply (H : vsrnet.EncSpecs (GF := GF) (hG := hG)) (b : GoSlice) (bs : List w8) (x : pkg.events.Reply) (d : w64) (hd : uint.nat d < 9000) (hres : PlainStr x.Result') :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (App (Val (@! pkg.events.jenc_Reply)) (Val #b)) (Val #x)) (Val #d))
    {{ (b' : GoSlice), RET (PairV #b' #(interface.nil : GoInterface));
        b' ↦* (bs ++ VsrJson.ser (VsrJson.payJV (.reply (uint.nat x.ID') (uint.nat x.ClientID') (uint.nat x.ViewNum') x.Result'))) ∗
        ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_if_destruct
  · exfalso; (try simp only [models_lab.jsoncodec.MaxDepth] at *); word
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 123]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  repeat (first
    | wp_apply (H.AppendRaw _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (H.AppendQuotedUint _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (vsrnet.wp_jenc_Request H _ _ _ _ (by word) (by assumption)) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | (wp_apply (H.AppendString _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
       rw [models_lab.jsoncodec.jsonQuote_plain _ (by assumption)])
    ; try wp_auto)
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 125]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  iapply HΦ
  simp only [VsrJson.ser, VsrJson.payJV, VsrJson.reqJV, pkg.log.entryOf, VsrJson.logJV, VsrJson.mkObj, VsrJson.serMs,
    VsrJson.serMsT, VsrJson.qn, VsrJson.cQ, VsrJson.cColon, VsrJson.cComma, VsrJson.cLB,
    VsrJson.cRB, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
    show (W8 123 : w8) = 123#8 from rfl, show (W8 125 : w8) = 125#8 from rfl]
  iframe


theorem vsrnet.wp_jenc_Prepare (H : vsrnet.EncSpecs (GF := GF) (hG := hG)) (b : GoSlice) (bs : List w8) (x : pkg.events.Prepare) (d : w64) (hd : uint.nat d < 9000) (hop : PlainStr x.Request'.Op') :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (App (Val (@! pkg.events.jenc_Prepare)) (Val #b)) (Val #x)) (Val #d))
    {{ (b' : GoSlice), RET (PairV #b' #(interface.nil : GoInterface));
        b' ↦* (bs ++ VsrJson.ser (VsrJson.payJV (.prepare (uint.nat x.ViewNum') (uint.nat x.OpNum') (uint.nat x.CommitNum') ⟨x.Request'.Op', uint.nat x.Request'.ClientID', uint.nat x.Request'.ID'⟩ (uint.nat x.ReplicaID')))) ∗
        ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_if_destruct
  · exfalso; (try simp only [models_lab.jsoncodec.MaxDepth] at *); word
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 123]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  repeat (first
    | wp_apply (H.AppendRaw _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (H.AppendQuotedUint _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (vsrnet.wp_jenc_Request H _ _ _ _ (by word) (by assumption)) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | (wp_apply (H.AppendString _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
       rw [models_lab.jsoncodec.jsonQuote_plain _ (by assumption)])
    ; try wp_auto)
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 125]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  iapply HΦ
  simp only [VsrJson.ser, VsrJson.payJV, VsrJson.reqJV, pkg.log.entryOf, VsrJson.logJV, VsrJson.mkObj, VsrJson.serMs,
    VsrJson.serMsT, VsrJson.qn, VsrJson.cQ, VsrJson.cColon, VsrJson.cComma, VsrJson.cLB,
    VsrJson.cRB, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
    show (W8 123 : w8) = 123#8 from rfl, show (W8 125 : w8) = 125#8 from rfl]
  iframe


theorem vsrnet.wp_jenc_PrepareOK (H : vsrnet.EncSpecs (GF := GF) (hG := hG)) (b : GoSlice) (bs : List w8) (x : pkg.events.PrepareOK) (d : w64) (hd : uint.nat d < 9000)  :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (App (Val (@! pkg.events.jenc_PrepareOK)) (Val #b)) (Val #x)) (Val #d))
    {{ (b' : GoSlice), RET (PairV #b' #(interface.nil : GoInterface));
        b' ↦* (bs ++ VsrJson.ser (VsrJson.payJV (.prepareOK (uint.nat x.ViewNum') (uint.nat x.OpNum') (uint.nat x.ReplicaID')))) ∗
        ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_if_destruct
  · exfalso; (try simp only [models_lab.jsoncodec.MaxDepth] at *); word
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 123]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  repeat (first
    | wp_apply (H.AppendRaw _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (H.AppendQuotedUint _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (vsrnet.wp_jenc_Request H _ _ _ _ (by word) (by assumption)) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | (wp_apply (H.AppendString _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
       rw [models_lab.jsoncodec.jsonQuote_plain _ (by assumption)])
    ; try wp_auto)
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 125]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  iapply HΦ
  simp only [VsrJson.ser, VsrJson.payJV, VsrJson.reqJV, pkg.log.entryOf, VsrJson.logJV, VsrJson.mkObj, VsrJson.serMs,
    VsrJson.serMsT, VsrJson.qn, VsrJson.cQ, VsrJson.cColon, VsrJson.cComma, VsrJson.cLB,
    VsrJson.cRB, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
    show (W8 123 : w8) = 123#8 from rfl, show (W8 125 : w8) = 125#8 from rfl]
  iframe


theorem vsrnet.wp_jenc_Commit (H : vsrnet.EncSpecs (GF := GF) (hG := hG)) (b : GoSlice) (bs : List w8) (x : pkg.events.Commit) (d : w64) (hd : uint.nat d < 9000)  :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (App (Val (@! pkg.events.jenc_Commit)) (Val #b)) (Val #x)) (Val #d))
    {{ (b' : GoSlice), RET (PairV #b' #(interface.nil : GoInterface));
        b' ↦* (bs ++ VsrJson.ser (VsrJson.payJV (.commit (uint.nat x.ViewNum') (uint.nat x.CommitNum') (uint.nat x.ReplicaID')))) ∗
        ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_if_destruct
  · exfalso; (try simp only [models_lab.jsoncodec.MaxDepth] at *); word
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 123]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  repeat (first
    | wp_apply (H.AppendRaw _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (H.AppendQuotedUint _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (vsrnet.wp_jenc_Request H _ _ _ _ (by word) (by assumption)) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | (wp_apply (H.AppendString _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
       rw [models_lab.jsoncodec.jsonQuote_plain _ (by assumption)])
    ; try wp_auto)
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 125]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  iapply HΦ
  simp only [VsrJson.ser, VsrJson.payJV, VsrJson.reqJV, pkg.log.entryOf, VsrJson.logJV, VsrJson.mkObj, VsrJson.serMs,
    VsrJson.serMsT, VsrJson.qn, VsrJson.cQ, VsrJson.cColon, VsrJson.cComma, VsrJson.cLB,
    VsrJson.cRB, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
    show (W8 123 : w8) = 123#8 from rfl, show (W8 125 : w8) = 125#8 from rfl]
  iframe


theorem vsrnet.wp_jenc_StartViewChange (H : vsrnet.EncSpecs (GF := GF) (hG := hG)) (b : GoSlice) (bs : List w8) (x : pkg.events.StartViewChange) (d : w64) (hd : uint.nat d < 9000)  :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (App (Val (@! pkg.events.jenc_StartViewChange)) (Val #b)) (Val #x)) (Val #d))
    {{ (b' : GoSlice), RET (PairV #b' #(interface.nil : GoInterface));
        b' ↦* (bs ++ VsrJson.ser (VsrJson.payJV (.startViewChange (uint.nat x.ViewNum') (uint.nat x.ReplicaID')))) ∗
        ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_if_destruct
  · exfalso; (try simp only [models_lab.jsoncodec.MaxDepth] at *); word
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 123]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  repeat (first
    | wp_apply (H.AppendRaw _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (H.AppendQuotedUint _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (vsrnet.wp_jenc_Request H _ _ _ _ (by word) (by assumption)) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | (wp_apply (H.AppendString _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
       rw [models_lab.jsoncodec.jsonQuote_plain _ (by assumption)])
    ; try wp_auto)
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 125]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  iapply HΦ
  simp only [VsrJson.ser, VsrJson.payJV, VsrJson.reqJV, pkg.log.entryOf, VsrJson.logJV, VsrJson.mkObj, VsrJson.serMs,
    VsrJson.serMsT, VsrJson.qn, VsrJson.cQ, VsrJson.cColon, VsrJson.cComma, VsrJson.cLB,
    VsrJson.cRB, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
    show (W8 123 : w8) = 123#8 from rfl, show (W8 125 : w8) = 125#8 from rfl]
  iframe


theorem vsrnet.wp_jenc_GetState (H : vsrnet.EncSpecs (GF := GF) (hG := hG)) (b : GoSlice) (bs : List w8) (x : pkg.events.GetState) (d : w64) (hd : uint.nat d < 9000)  :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (App (Val (@! pkg.events.jenc_GetState)) (Val #b)) (Val #x)) (Val #d))
    {{ (b' : GoSlice), RET (PairV #b' #(interface.nil : GoInterface));
        b' ↦* (bs ++ VsrJson.ser (VsrJson.payJV (.getState (uint.nat x.ViewNum') (uint.nat x.OpNum') (uint.nat x.ReplicaID')))) ∗
        ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_if_destruct
  · exfalso; (try simp only [models_lab.jsoncodec.MaxDepth] at *); word
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 123]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  repeat (first
    | wp_apply (H.AppendRaw _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (H.AppendQuotedUint _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (vsrnet.wp_jenc_Request H _ _ _ _ (by word) (by assumption)) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | (wp_apply (H.AppendString _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
       rw [models_lab.jsoncodec.jsonQuote_plain _ (by assumption)])
    ; try wp_auto)
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 125]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  iapply HΦ
  simp only [VsrJson.ser, VsrJson.payJV, VsrJson.reqJV, pkg.log.entryOf, VsrJson.logJV, VsrJson.mkObj, VsrJson.serMs,
    VsrJson.serMsT, VsrJson.qn, VsrJson.cQ, VsrJson.cColon, VsrJson.cComma, VsrJson.cLB,
    VsrJson.cRB, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
    show (W8 123 : w8) = 123#8 from rfl, show (W8 125 : w8) = 125#8 from rfl]
  iframe


theorem vsrnet.wp_jenc_Heartbeat (H : vsrnet.EncSpecs (GF := GF) (hG := hG)) (b : GoSlice) (bs : List w8) (x : pkg.events.Heartbeat) (d : w64) (hd : uint.nat d < 9000)  :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (App (Val (@! pkg.events.jenc_Heartbeat)) (Val #b)) (Val #x)) (Val #d))
    {{ (b' : GoSlice), RET (PairV #b' #(interface.nil : GoInterface));
        b' ↦* (bs ++ VsrJson.ser (VsrJson.payJV (.heartbeat))) ∗
        ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_if_destruct
  · exfalso; (try simp only [models_lab.jsoncodec.MaxDepth] at *); word
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 123]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  repeat (first
    | wp_apply (H.AppendRaw _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (H.AppendQuotedUint _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (vsrnet.wp_jenc_Request H _ _ _ _ (by word) (by assumption)) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | (wp_apply (H.AppendString _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
       rw [models_lab.jsoncodec.jsonQuote_plain _ (by assumption)])
    ; try wp_auto)
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 125]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  iapply HΦ
  simp only [VsrJson.ser, VsrJson.payJV, VsrJson.reqJV, pkg.log.entryOf, VsrJson.logJV, VsrJson.mkObj, VsrJson.serMs,
    VsrJson.serMsT, VsrJson.qn, VsrJson.cQ, VsrJson.cColon, VsrJson.cComma, VsrJson.cLB,
    VsrJson.cRB, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
    show (W8 123 : w8) = 123#8 from rfl, show (W8 125 : w8) = 125#8 from rfl]
  iframe


theorem vsrnet.wp_jenc_DoViewChange (H : vsrnet.EncSpecs (GF := GF) (hG := hG)) (b : GoSlice) (bs : List w8) (x : pkg.events.DoViewChange) (d : w64) (hd : uint.nat d < 9000) (dq : DFrac)
    (es : List Entry) (hes : ∀ e ∈ es, PlainStr e.op) (hon : uint.nat x.OpNum' = es.length) :
    {{ (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
        vsrnet.logsRoute (GF := GF) ∗
        pkg.log.ownLogs x.Logs' dq es ∗ b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (App (Val (@! pkg.events.jenc_DoViewChange)) (Val #b)) (Val #x)) (Val #d))
    {{ (b' : GoSlice), RET (PairV #b' #(interface.nil : GoInterface));
        b' ↦* (bs ++ VsrJson.ser (VsrJson.payJV (.doViewChange ⟨uint.nat x.ViewNum', es, uint.nat x.LastStableViewNum', uint.nat x.CommitNum', uint.nat x.ReplicaID'⟩))) ∗
        ownSliceCap w8 b' (DFrac.own 1) ∗ pkg.log.ownLogs x.Logs' dq es }} := by
  wp_start as ⟨#Hset, Hl, Hb, Hcap⟩
  wp_auto
  wp_if_destruct
  · exfalso; (try simp only [models_lab.jsoncodec.MaxDepth] at *); word
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 123]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  repeat (first
    | wp_apply (H.AppendRaw _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (H.AppendQuotedUint _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (vsrnet.wp_jenc_logs H _ _ _ _ es _ hes (by word)) $$ [$Hset $Hl $Hb $Hcap] as %b' ⟨Hb, Hcap, Hl⟩
    | (wp_apply (H.AppendString _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
       rw [models_lab.jsoncodec.jsonQuote_plain _ (by assumption)])
    ; try wp_auto)
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 125]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  iapply HΦ
  simp only [VsrJson.ser, VsrJson.payJV, VsrJson.reqJV, hon, VsrJson.mkObj, VsrJson.serMs,
    VsrJson.serMsT, VsrJson.qn, VsrJson.cQ, VsrJson.cColon, VsrJson.cComma, VsrJson.cLB,
    VsrJson.cRB, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
    show (W8 123 : w8) = 123#8 from rfl, show (W8 125 : w8) = 125#8 from rfl]
  iframe

theorem vsrnet.wp_jenc_StartView (H : vsrnet.EncSpecs (GF := GF) (hG := hG)) (b : GoSlice) (bs : List w8) (x : pkg.events.StartView) (d : w64) (hd : uint.nat d < 9000) (dq : DFrac)
    (es : List Entry) (hes : ∀ e ∈ es, PlainStr e.op)  :
    {{ (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
        vsrnet.logsRoute (GF := GF) ∗
        pkg.log.ownLogs x.Logs' dq es ∗ b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (App (Val (@! pkg.events.jenc_StartView)) (Val #b)) (Val #x)) (Val #d))
    {{ (b' : GoSlice), RET (PairV #b' #(interface.nil : GoInterface));
        b' ↦* (bs ++ VsrJson.ser (VsrJson.payJV (.startView (uint.nat x.ViewNum') (uint.nat x.OpNum') (uint.nat x.CommitNum') es (uint.nat x.ReplicaID')))) ∗
        ownSliceCap w8 b' (DFrac.own 1) ∗ pkg.log.ownLogs x.Logs' dq es }} := by
  wp_start as ⟨#Hset, Hl, Hb, Hcap⟩
  wp_auto
  wp_if_destruct
  · exfalso; (try simp only [models_lab.jsoncodec.MaxDepth] at *); word
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 123]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  repeat (first
    | wp_apply (H.AppendRaw _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (H.AppendQuotedUint _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (vsrnet.wp_jenc_logs H _ _ _ _ es _ hes (by word)) $$ [$Hset $Hl $Hb $Hcap] as %b' ⟨Hb, Hcap, Hl⟩
    | (wp_apply (H.AppendString _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
       rw [models_lab.jsoncodec.jsonQuote_plain _ (by assumption)])
    ; try wp_auto)
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 125]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  iapply HΦ
  simp only [VsrJson.ser, VsrJson.payJV, VsrJson.reqJV, VsrJson.mkObj, VsrJson.serMs,
    VsrJson.serMsT, VsrJson.qn, VsrJson.cQ, VsrJson.cColon, VsrJson.cComma, VsrJson.cLB,
    VsrJson.cRB, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
    show (W8 123 : w8) = 123#8 from rfl, show (W8 125 : w8) = 125#8 from rfl]
  iframe

theorem vsrnet.wp_jenc_NewState (H : vsrnet.EncSpecs (GF := GF) (hG := hG)) (b : GoSlice) (bs : List w8) (x : pkg.events.NewState) (d : w64) (hd : uint.nat d < 9000) (dq : DFrac)
    (es : List Entry) (hes : ∀ e ∈ es, PlainStr e.op)  :
    {{ (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
        vsrnet.logsRoute (GF := GF) ∗
        pkg.log.ownLogs x.Logs' dq es ∗ b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (App (Val (@! pkg.events.jenc_NewState)) (Val #b)) (Val #x)) (Val #d))
    {{ (b' : GoSlice), RET (PairV #b' #(interface.nil : GoInterface));
        b' ↦* (bs ++ VsrJson.ser (VsrJson.payJV (.newState (uint.nat x.ViewNum') es (uint.nat x.CommitNum') (uint.nat x.OpNum') (uint.nat x.ReplicaID')))) ∗
        ownSliceCap w8 b' (DFrac.own 1) ∗ pkg.log.ownLogs x.Logs' dq es }} := by
  wp_start as ⟨#Hset, Hl, Hb, Hcap⟩
  wp_auto
  wp_if_destruct
  · exfalso; (try simp only [models_lab.jsoncodec.MaxDepth] at *); word
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 123]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  repeat (first
    | wp_apply (H.AppendRaw _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (H.AppendQuotedUint _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (vsrnet.wp_jenc_logs H _ _ _ _ es _ hes (by word)) $$ [$Hset $Hl $Hb $Hcap] as %b' ⟨Hb, Hcap, Hl⟩
    | (wp_apply (H.AppendString _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
       rw [models_lab.jsoncodec.jsonQuote_plain _ (by assumption)])
    ; try wp_auto)
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 125]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  iapply HΦ
  simp only [VsrJson.ser, VsrJson.payJV, VsrJson.reqJV, VsrJson.mkObj, VsrJson.serMs,
    VsrJson.serMsT, VsrJson.qn, VsrJson.cQ, VsrJson.cColon, VsrJson.cComma, VsrJson.cLB,
    VsrJson.cRB, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
    show (W8 123 : w8) = 123#8 from rfl, show (W8 125 : w8) = 125#8 from rfl]
  iframe

set_option maxHeartbeats 10000000 in
theorem vsrnet.wp_jencAny_payload (H : vsrnet.EncSpecs (GF := GF) (hG := hG)) (b : GoSlice) (bs : List w8) (d : GoInterface) (m : Msg)
    (dp : w64) (hdp : uint.nat dp < 9000) (hm : PlainMsg m) :
    {{ (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
        vsrnet.logsRoute (GF := GF) ∗
        pkg.events.payloadOf d m ∗ b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (App (Val (@! pkg.events.jencAny)) (Val #b)) (Val #d)) (Val #dp))
    {{ (b' : GoSlice), RET (PairV #b' #(interface.nil : GoInterface));
        b' ↦* (bs ++ VsrJson.ser (VsrJson.payJV m)) ∗ ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as ⟨#Hset, #Hpay, Hb, Hcap⟩
  cases m with
  | request id cid op =>
    try simp only [PlainMsg] at hm
    try simp only [pkg.events.payloadOf]
    icases Hpay with ⟨%x, %hx⟩
    obtain ⟨rfl, h1, h2, h3⟩ := hx
    subst h1 h2 h3
    wp_auto
    wp_apply (vsrnet.wp_jenc_Request H _ _ x dp (by omega) hm) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    try wp_auto
    iapply HΦ
    iframe
  | reply id cid v res =>
    try simp only [PlainMsg] at hm
    try simp only [pkg.events.payloadOf]
    icases Hpay with ⟨%x, %hx⟩
    obtain ⟨rfl, h1, h2, h3, h4⟩ := hx
    subst h1 h2 h3 h4
    wp_auto
    wp_apply (vsrnet.wp_jenc_Reply H _ _ x dp hdp hm) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    try wp_auto
    iapply HΦ
    iframe
  | prepare v k c e rid =>
    try simp only [PlainMsg] at hm
    try simp only [pkg.events.payloadOf]
    icases Hpay with ⟨%x, %hx⟩
    obtain ⟨op, cid, req⟩ := e
    obtain ⟨rfl, h1, h2, h3, ⟨h4, h5, h6⟩, h7⟩ := hx
    subst h1 h2 h3 h4 h5 h6 h7
    wp_auto
    wp_apply (vsrnet.wp_jenc_Prepare H _ _ x dp hdp hm) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    try wp_auto
    iapply HΦ
    iframe
  | prepareOK v k rid =>
    try simp only [PlainMsg] at hm
    try simp only [pkg.events.payloadOf]
    icases Hpay with ⟨%x, %hx⟩
    obtain ⟨rfl, h1, h2, h3⟩ := hx
    subst h1 h2 h3
    wp_auto
    wp_apply (vsrnet.wp_jenc_PrepareOK H _ _ x dp hdp) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    try wp_auto
    iapply HΦ
    iframe
  | commit v c rid =>
    try simp only [PlainMsg] at hm
    try simp only [pkg.events.payloadOf]
    icases Hpay with ⟨%x, %hx⟩
    obtain ⟨rfl, h1, h2, h3⟩ := hx
    subst h1 h2 h3
    wp_auto
    wp_apply (vsrnet.wp_jenc_Commit H _ _ x dp hdp) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    try wp_auto
    iapply HΦ
    iframe
  | startViewChange v rid =>
    try simp only [PlainMsg] at hm
    try simp only [pkg.events.payloadOf]
    icases Hpay with ⟨%x, %hx⟩
    obtain ⟨rfl, h1, h2⟩ := hx
    subst h1 h2
    wp_auto
    wp_apply (vsrnet.wp_jenc_StartViewChange H _ _ x dp hdp) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    try wp_auto
    iapply HΦ
    iframe
  | getState v k rid =>
    try simp only [PlainMsg] at hm
    try simp only [pkg.events.payloadOf]
    icases Hpay with ⟨%x, %hx⟩
    obtain ⟨rfl, h1, h2, h3⟩ := hx
    subst h1 h2 h3
    wp_auto
    wp_apply (vsrnet.wp_jenc_GetState H _ _ x dp hdp) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    try wp_auto
    iapply HΦ
    iframe
  | heartbeat =>
    try simp only [PlainMsg] at hm
    try simp only [pkg.events.payloadOf]
    icases Hpay with ⟨%x, %hx⟩
    subst hx
    wp_auto
    wp_apply (vsrnet.wp_jenc_Heartbeat H _ _ x dp hdp) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    try wp_auto
    iapply HΦ
    iframe
  | doViewChange d =>
    try simp only [PlainMsg] at hm
    try simp only [pkg.events.payloadOf]
    icases Hpay with ⟨%x, %hx, #Hl⟩
    obtain ⟨dv, dl, dlnv, dc, drid⟩ := d
    obtain ⟨rfl, h1, h2, h3, h4, h5⟩ := hx
    simp only at h1 h2 h3 h4 h5 hm
    subst h1 h2 h4 h5
    wp_auto
    wp_apply (vsrnet.wp_jenc_DoViewChange H _ _ x dp hdp DFrac.discard dl hm h3) $$ [$Hset $Hl $Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
    try wp_auto
    iapply HΦ
    iframe
  | startView v k c logs rid =>
    try simp only [PlainMsg] at hm
    try simp only [pkg.events.payloadOf]
    icases Hpay with ⟨%x, %hx, #Hl⟩
    obtain ⟨rfl, h1, h2, h3, h4⟩ := hx
    subst h1 h2 h3 h4
    wp_auto
    wp_apply (vsrnet.wp_jenc_StartView H _ _ x dp hdp DFrac.discard logs hm) $$ [$Hset $Hl $Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
    try wp_auto
    iapply HΦ
    iframe
  | newState v logs c k rid =>
    try simp only [PlainMsg] at hm
    try simp only [pkg.events.payloadOf]
    icases Hpay with ⟨%x, %hx, #Hl⟩
    obtain ⟨rfl, h1, h2, h3, h4⟩ := hx
    subst h1 h2 h3 h4
    wp_auto
    wp_apply (vsrnet.wp_jenc_NewState H _ _ x dp hdp DFrac.discard logs hm) $$ [$Hset $Hl $Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
    try wp_auto
    iapply HΦ
    iframe

theorem vsrnet.wp_jenc_Event (H : vsrnet.EncSpecs (GF := GF) (hG := hG)) (b : GoSlice) (bs : List w8) (d : GoInterface) (m : Msg)
    (hm : PlainMsg m) :
    {{ (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
        vsrnet.logsRoute (GF := GF) ∗
        pkg.events.payloadOf d m ∗ b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (App (Val (@! pkg.events.jenc_Event)) (Val #b))
        (Val #(pkg.events.Event.mk (pkg.events.typeOf m) d))) (Val #(W64 0)))
    {{ (b' : GoSlice), RET (PairV #b' #(interface.nil : GoInterface));
        b' ↦* (bs ++ VsrJson.ser (VsrJson.evJV m)) ∗ ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as ⟨#Hset, #Hpay, Hb, Hcap⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 123]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  wp_apply (H.AppendRaw _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
  try wp_auto
  wp_apply (H.AppendUint _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
  rw [models_lab.jsoncodec.decU64_eq_decN]
  try wp_auto
  wp_apply (H.AppendRaw _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
  try wp_auto
  wp_apply (vsrnet.wp_jencAny_payload H _ _ d m _ (by word) hm) $$ [$Hset $Hpay $Hb $Hcap] as %b' ⟨Hb, Hcap⟩
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 125]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  iapply HΦ
  have ht : uint.nat (W64 (uint.Z (pkg.events.typeOf m))) = VsrJson.typeN m := by
    have := vsrnet.typeN_le m
    rw [vsrnet.typeOf_eq]; word
  rw [ht]
  simp only [VsrJson.ser, VsrJson.evJV, VsrJson.mkObj, VsrJson.serMs, VsrJson.serMsT,
    VsrJson.cQ, VsrJson.cColon, VsrJson.cComma, VsrJson.cLB, VsrJson.cRB, List.append_assoc,
    List.cons_append, List.nil_append, List.singleton_append,
    show (W8 123 : w8) = 123#8 from rfl, show (W8 125 : w8) = 125#8 from rfl]
  iframe


/-- **`TypeMethods.event`, proved**: `(*events.Event).JSONModelMarshalPtr` meets the kit's contract
(`encP`'s event case: an event of a message with plain strings is written as `encEvent m`; the
`[]Log` case is at another type). -/
theorem vsrnet.eventMarshalOk (H : vsrnet.EncSpecs (GF := GF) (hG := hG))
    (HD : vsrnet.DecSpecs (GF := GF) (hG := hG)) (l : Loc) :
    ⊢ encoding.json.marshalAt (vsrnet.jsonCodec (GF := GF))
      #(methods (go.GoType.PointerType pkg.events.Event.ty) go!"JSONModelMarshalPtr" #l)
      (interface.mkOk (go.GoType.PointerType pkg.events.Event.ty) #l) := by
  unfold encoding.json.marshalAt
  iintro %Ψ %Φ Henc HΦ
  rw [vsrnet.enc_eq]; unfold vsrnet.encP
  icases Henc with (⟨%_, %_, %_, %ev, %m, %hv, %hm, #Hpkg, #Hset, #Hev, HΨ⟩ |
    ⟨%_, %sl, %dq, %es, %hv, -⟩)
  rotate_left
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hv).1
    simp only [reduceCtorEq] at hty
  have hlp := ((interface_mkOk_inj _ _ _ _).1 hv).2
  rw [hlp]
  unfold pkg.events.isEvent
  icases Hev with ⟨%d, #Hp, #Hpay⟩
  ihave #Hroute := vsrnet.logsRoute_of HD $$ Hset
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_method_call
  wp_auto
  try rw [decide_eq_false Hnn]
  try wp_auto
  wp_apply wp_slice_make2 (V := w8) (W64 0) $$ [] as %b ⟨Hb, Hcap⟩
  · ipureintro; decide
  simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
  try wp_auto
  wp_apply (vsrnet.wp_jenc_Event H _ [] d m hm) $$ [$Hroute $Hpay $Hb $Hcap] as %b' ⟨Hb, Hcap⟩
  try wp_auto
  icases HΦ with ⟨HΦ, -⟩
  simp only [List.nil_append]
  rw [show VsrJson.ser (VsrJson.evJV m) = VsrWire.encEvent m by
    simp [VsrWire.encEvent, VsrJson.encEvent_plain m hm]]
  iapply HΦ $$ Hb Hcap HΨ

end proof

end Perennial.github_com.tangledbytes.go_vsr.examples
