/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Spec/log.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension. The JSON vocabulary (`JsonCodec`, `jsonValid`) is the
repository's `models_lab.jsoncodec` one; `codecSet` and `kitCodecOk` are `Spec/jsonlib.lean`'s (the
future `encoding/json` hypotheses' vocabulary). Statements unchanged.
-/
/-
Cross-package specs of `pkg/log`: a `Logs` slice as the model's list of entries (`ownLogs`),
and the methods its callers use: `NewLogs`, `Len`, `Add`, `OpAt`, `ClientIDAt`, `RequestIDAt`,
`After`, `Merge` (the replica), `MarshalJSON` and `UnmarshalJSON` (the kit's JSON codec, through
`log.Logs`'s fields of the events' payloads).

The JSON methods are stated as the codec calls them: their bytes are the codec's encoding of the
entries (`encLogs`, the JSON prover's choice; `JsonCodec` is a parameter here, instantiated by
`VsrProof/Spec/json.lean`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.log.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Model.Basic
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.jsoncodec.Enc
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.jsonlib

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The model's entry of a `log.Log` value. -/
def log.entryOf [GooseExts] (l : log.Log) : VsrModel.Entry :=
  ⟨l.Data', uint.nat l.ClientID', uint.nat l.RequestID'⟩

/-- The JSON encoding of a `log.Logs` holding `es` (`Logs.MarshalJSON`'s bytes, compact).
-- sealed: the JSON codec's choice (consistent with `VsrWire.encEvent`) -/
def log.encLogs (es : List VsrModel.Entry) : List w8 := VsrJson.encLogs es

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : log.Assumptions]

/-- The `log.Logs` slice `sl` holds the entries `es` (elements at fraction `dq`); it is not nil
(every producer makes or appends to a non-nil slice; the codec encodes a nil slice as `null`;
codec-2, D5). -/
def log.ownLogs (sl : GoSlice) (dq : DFrac) (es : List VsrModel.Entry) : IProp GF :=
  iprop(∃ ls : List log.Log, sl ↦*{dq} ls ∗ ⌜ls.map log.entryOf = es⌝ ∗ ⌜sl ≠ slice.nil⌝)

instance log.ownLogs_timeless (sl : GoSlice) (dq : DFrac) (es : List VsrModel.Entry) :
    Timeless (log.ownLogs (GF := GF) sl dq es) := by
  unfold log.ownLogs; infer_instance
instance log.ownLogs_persistent (sl : GoSlice) (es : List VsrModel.Entry) :
    Persistent (log.ownLogs (GF := GF) sl DFrac.discard es) := by
  unfold log.ownLogs; infer_instance

/-- A `log.Logs` slice's elements can be made read-only for good. -/
theorem log.ownLogs_persist (sl : GoSlice) (dq : DFrac) (es : List VsrModel.Entry) :
    log.ownLogs (GF := GF) sl dq es ⊢ |==> log.ownLogs sl DFrac.discard es := by
  unfold log.ownLogs
  iintro ⟨%ls, H, %h1, %h2⟩
  imod ownSlice_persist _ _ _ $$ H with H
  imodintro
  iexists ls
  iframe
  ipureintro; exact ⟨h1, h2⟩

/-- The elements' ids are below `2^64` (they are `uint64`s). -/
theorem log.ownLogs_bound (sl : GoSlice) (dq : DFrac) (es : List VsrModel.Entry) :
    log.ownLogs (GF := GF) sl dq es ⊢ ⌜∀ e ∈ es, e.cid < 2 ^ 64 ∧ e.req < 2 ^ 64⌝ ∗ log.ownLogs sl dq es :=
  by
  unfold log.ownLogs
  iintro ⟨%ls, H, %h1, %h2⟩
  isplitr
  · ipureintro
    intro e he
    rw [← h1] at he
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 he
    simp only [log.entryOf]
    constructor <;> word
  · iexists ls
    iframe
    ipureintro; exact ⟨h1, h2⟩

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : log.Assumptions]

set_option goose.wp.extras true

/-- `NewLogs()`: an empty slice, with its capacity. -/
abbrev log.NewLogs.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log }}
    (App (Val (@! log.NewLogs)) (Val #()))
  {{ (sl : GoSlice), RET #sl; log.ownLogs sl (DFrac.own 1) [] ∗
      ownSliceCap log.Log sl (DFrac.own 1) }}

/-- `l.Len()`: the number of entries. -/
abbrev log.Logs.Len.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (es : List VsrModel.Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
      log.ownLogs sl dq es }}
    (App (Val (sl @!! log.Logs.ty @!! go!"Len")) (Val #()))
  {{ RET #(W64 es.length); log.ownLogs sl dq es }}

/-- `l.Add(e)` (`l` a `*Logs` holding `sl`, with its capacity): `e`'s entry appended. The old
elements may be read-only (`dq`): `append` writes only past them. -/
abbrev log.Logs.Add.spec : Prop :=
  ∀ (l : Loc) (sl : GoSlice) (dq : DFrac) (es : List VsrModel.Entry) (e : log.Log),
  ✓ dq →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
      l ↦ sl ∗ log.ownLogs sl dq es ∗ ownSliceCap log.Log sl (DFrac.own 1) }}
    (App (Val (l @!! go.GoType.PointerType log.Logs.ty @!! go!"Add")) (Val #e))
  {{ RET #(); ∃ sl' : GoSlice, l ↦ sl' ∗ log.ownLogs sl' dq (es ++ [log.entryOf e]) ∗
      ownSliceCap log.Log sl' (DFrac.own 1) }}

/-- `l.OpAt(i)` (`1 ≤ i ≤ len`): the operation of the `i`-th entry. -/
abbrev log.Logs.OpAt.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (es : List VsrModel.Entry) (i : w64) (e : VsrModel.Entry),
  0 < sint.Z i → es[sint.nat i - 1]? = some e →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
      log.ownLogs sl dq es }}
    (App (Val (sl @!! log.Logs.ty @!! go!"OpAt")) (Val #i))
  {{ RET #e.op; log.ownLogs sl dq es }}

/-- `l.ClientIDAt(i)` (`1 ≤ i ≤ len`): the client id of the `i`-th entry. -/
abbrev log.Logs.ClientIDAt.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (es : List VsrModel.Entry) (i : w64) (e : VsrModel.Entry),
  0 < sint.Z i → es[sint.nat i - 1]? = some e →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
      log.ownLogs sl dq es }}
    (App (Val (sl @!! log.Logs.ty @!! go!"ClientIDAt")) (Val #i))
  {{ RET #(W64 e.cid); log.ownLogs sl dq es }}

/-- `l.RequestIDAt(i)` (`1 ≤ i ≤ len`): the request number of the `i`-th entry. -/
abbrev log.Logs.RequestIDAt.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (es : List VsrModel.Entry) (i : w64) (e : VsrModel.Entry),
  0 < sint.Z i → es[sint.nat i - 1]? = some e →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
      log.ownLogs sl dq es }}
    (App (Val (sl @!! log.Logs.ty @!! go!"RequestIDAt")) (Val #i))
  {{ RET #(W64 e.req); log.ownLogs sl dq es }}

/-- `l.After(i)` (`l` a `*Logs` holding `sl`, `0 ≤ i ≤ len`): the entries after the `i`-th, a
sub-slice sharing `sl`'s array, read-only (the caller's elements are read-only). -/
abbrev log.Logs.After.spec : Prop :=
  ∀ (l : Loc) (dl : DFrac) (sl : GoSlice) (es : List VsrModel.Entry) (i : w64),
  0 ≤ sint.Z i → sint.nat i ≤ es.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
      l ↦{dl} sl ∗ log.ownLogs sl DFrac.discard es }}
    (App (Val (l @!! go.GoType.PointerType log.Logs.ty @!! go!"After")) (Val #i))
  {{ (sl' : GoSlice), RET #sl'; l ↦{dl} sl ∗ log.ownLogs sl' DFrac.discard (es.drop (sint.nat i)) }}

/-- `l.Merge(logs)` (`l` a `*Logs` holding `sl`, with its capacity): `logs`' entries appended. -/
abbrev log.Logs.Merge.spec : Prop :=
  ∀ (l : Loc) (sl : GoSlice) (dq : DFrac) (es : List VsrModel.Entry) (sl2 : GoSlice)
    (dq2 : DFrac) (es2 : List VsrModel.Entry),
  ✓ dq →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
      l ↦ sl ∗ log.ownLogs sl dq es ∗ ownSliceCap log.Log sl (DFrac.own 1) ∗
      log.ownLogs sl2 dq2 es2 }}
    (App (Val (l @!! go.GoType.PointerType log.Logs.ty @!! go!"Merge")) (Val #sl2))
  {{ RET #(); ∃ sl' : GoSlice, l ↦ sl' ∗ log.ownLogs sl' dq (es ++ es2) ∗
      ownSliceCap log.Log sl' (DFrac.own 1) ∗ log.ownLogs sl2 dq2 es2 }}

variable [encoding.json.Assumptions] [models_lab.jsoncodec.JsonCodec GF]

/-- `l.MarshalJSON()` (`json.Marshal([]Log(l))`), as the kit's codec calls it (with its scanner
`F`, the codec registered), the operations plain: the codec's encoding of the entries, in a
fresh slice, no error. The codec's fact it uses is a premise (`henc`: `vsrnet.enc_logs`, at the
kit's codec; codec-5, D5). -/
abbrev log.Logs.MarshalJSON.spec : Prop :=
  ∀ (F : List w8 → Bool → w64 × w64) (sl : GoSlice) (dq : DFrac) (es : List VsrModel.Entry),
  (∀ (sl' : GoSlice) (dq' : DFrac) (es' : List VsrModel.Entry),
    (∀ e ∈ es', VsrModel.PlainStr e.op) →
    log.ownLogs (GF := GF) sl' dq' es' ⊢
    models_lab.jsoncodec.JsonCodec.enc (interface.mkOk (go.GoType.SliceType log.Log.ty) #sl')
      (fun r => iprop(⌜r = some (log.encLogs es')⌝ ∗ log.ownLogs sl' dq' es'))) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
      encoding.json.codecSet (GF := GF) ∗ encoding.json.kitCodecOk F ∗
      log.ownLogs sl dq es ∗ ⌜∀ e ∈ es, VsrModel.PlainStr e.op⌝ }}
    (App (Val (sl @!! log.Logs.ty @!! go!"MarshalJSON")) (Val #()))
  {{ (b : GoSlice), RET (PairV #b #(interface.nil : GoInterface)); log.ownLogs sl dq es ∗
      b ↦* log.encLogs es ∗ ownSliceCap w8 b (DFrac.own 1) }}

/-- `l.UnmarshalJSON(data)` (`l` a `*Logs`), on the codec's encoding of some entries `es` (their
ids in `uint64`, their operations plain; codec-1, D5): `*l` becomes a fresh slice holding them
(with its capacity), no error. The codec's facts it uses are premises (`hval`:
`vsrnet.encLogs_valid`, `hdec`: `vsrnet.dec_logs`, at the kit's codec and scanner; codec-5,
D5). -/
abbrev log.Logs.UnmarshalJSON.spec : Prop :=
  ∀ (F : List w8 → Bool → w64 × w64) (l : Loc) (sl0 : GoSlice) (data : GoSlice) (dq : DFrac)
    (es : List VsrModel.Entry),
  models_lab.jsoncodec.jsonValid F (log.encLogs es) →
  (∀ (p : Loc) (sl1 : GoSlice), sl1 = slice.nil →
    (p ↦ sl1 : IProp GF) ⊢
    models_lab.jsoncodec.JsonCodec.dec (log.encLogs es)
      (interface.mkOk (go.GoType.PointerType (go.GoType.SliceType log.Log.ty)) #p)
      (fun ok => iprop(⌜ok = true⌝ ∗ ∃ sl : GoSlice, p ↦ sl ∗
        log.ownLogs sl (DFrac.own 1) es ∗ ownSliceCap log.Log sl (DFrac.own 1)))) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
      encoding.json.codecSet (GF := GF) ∗ encoding.json.kitCodecOk F ∗
      l ↦ sl0 ∗ data ↦*{dq} log.encLogs es ∗
      ⌜∀ e ∈ es, e.cid < 2 ^ 64 ∧ e.req < 2 ^ 64 ∧ VsrModel.PlainStr e.op⌝ }}
    (App (Val (l @!! go.GoType.PointerType log.Logs.ty @!! go!"UnmarshalJSON")) (Val #data))
  {{ RET #(interface.nil : GoInterface); ∃ sl : GoSlice, l ↦ sl ∗
      log.ownLogs sl (DFrac.own 1) es ∗ ownSliceCap log.Log sl (DFrac.own 1) ∗
      data ↦*{dq} log.encLogs es }}

end spec

end Perennial.github_com.tangledbytes.go_vsr.pkg
