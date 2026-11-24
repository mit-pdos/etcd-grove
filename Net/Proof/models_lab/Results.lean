/-
The results of `models.lab`'s codec helpers (`models/`, project models; phase 5 item 1 of
notes/dsverify-net-port-plan.md), restated, with `#print axioms` of each (none beyond Lean's):

* `jsoncodec`: `IsSpace`, `AppendRaw`, `AppendBool`, `(*Error).Error`, and its package
  initialization; `Error_errAny` (a kept `*jsoncodec.Error` is some error); the scanner
  `SkipSpace`, `Scan` (`JsonScan.scanF`, `jsoncodec/Scan/Def.lean`) and the codec obligation
  `scanOk JsonScan.scanF scanFn` (`scanOk_scanF`); the decoding helpers `ValueEnd`, `At`, `Next`,
  `Empty`, `Str`, `Member`, `Digits`, `Uint`, `QuotedUint`, `String` (at valid input); the
  encoding helpers `AppendUint`, `AppendQuotedUint`, `AppendString` (its plain subset); `Valid` (on
  one complete value);
* `pbcodec`: `(*Error).Error`, its package initialization, and `Error_errAny`.

The codec obligations (`pbcodec.PbCodec`, `marshalOk`, `unmarshalOk`; `jsoncodec.JsonCodec`,
`jsonValid`, `marshalOk`, `unmarshalOk`, `scanOk`) are definitions, in `pbcodec/Codec.lean` and
`jsoncodec/Codec.lean`: each program proves them of its generated codec.
-/
module

public import Net.Proof.models_lab.pbcodec.Codec
public import Net.Proof.models_lab.pbcodec.Init
public import Net.Proof.models_lab.jsoncodec.Codec
public import Net.Proof.models_lab.jsoncodec.Init
public import Net.Proof.models_lab.jsoncodec.IsSpace
public import Net.Proof.models_lab.jsoncodec.AppendRaw
public import Net.Proof.models_lab.jsoncodec.AppendBool
public import Net.Proof.models_lab.jsoncodec.Error__Error
public import Net.Proof.models_lab.jsoncodec.SkipSpace
public import Net.Proof.models_lab.jsoncodec.Scan
public import Net.Proof.models_lab.jsoncodec.ScanOk
public import Net.Proof.models_lab.jsoncodec.Valid
public import Net.Proof.models_lab.jsoncodec.AppendUint
public import Net.Proof.models_lab.jsoncodec.AppendQuotedUint
public import Net.Proof.models_lab.jsoncodec.AppendString
public import Net.Proof.models_lab.jsoncodec.ValueEnd
public import Net.Proof.models_lab.jsoncodec.At
public import Net.Proof.models_lab.jsoncodec.Next
public import Net.Proof.models_lab.jsoncodec.Empty
public import Net.Proof.models_lab.jsoncodec.Str
public import Net.Proof.models_lab.jsoncodec.Member
public import Net.Proof.models_lab.jsoncodec.Digits
public import Net.Proof.models_lab.jsoncodec.Uint
public import Net.Proof.models_lab.jsoncodec.QuotedUint
public import Net.Proof.models_lab.jsoncodec.String
public import Net.Proof.models_lab.pbcodec.Error__Error

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace models_lab

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem jsoncodec.IsSpace.wp [jsoncodec.Assumptions] :
    jsoncodec.IsSpace.spec (GF := GF) (hG := hG) :=
  jsoncodec.IsSpace.wp_proof

theorem jsoncodec.AppendRaw.wp [jsoncodec.Assumptions] :
    jsoncodec.AppendRaw.spec (GF := GF) (hG := hG) :=
  jsoncodec.AppendRaw.wp_proof

theorem jsoncodec.AppendBool.wp [jsoncodec.Assumptions] :
    jsoncodec.AppendBool.spec (GF := GF) (hG := hG) :=
  jsoncodec.AppendBool.wp_proof

theorem jsoncodec.Error.Error.wp [jsoncodec.Assumptions] :
    jsoncodec.Error.Error.spec (GF := GF) (hG := hG) :=
  jsoncodec.Error.Error.wp_proof

theorem jsoncodec.SkipSpace.wp [jsoncodec.Assumptions] :
    jsoncodec.SkipSpace.spec (GF := GF) (hG := hG) :=
  jsoncodec.SkipSpace.wp_proof jsoncodec.IsSpace.wp_proof

theorem jsoncodec.Scan.wp [jsoncodec.Assumptions] :
    jsoncodec.Scan.spec (GF := GF) (hG := hG) :=
  jsoncodec.Scan.wp_proof jsoncodec.SkipSpace.wp

theorem jsoncodec.ValueEnd.wp [jsoncodec.Assumptions] :
    jsoncodec.ValueEnd.spec (GF := GF) (hG := hG) :=
  jsoncodec.ValueEnd.wp_proof jsoncodec.Scan.wp

theorem jsoncodec.At.wp [jsoncodec.Assumptions] :
    jsoncodec.At.spec (GF := GF) (hG := hG) :=
  jsoncodec.At.wp_proof jsoncodec.SkipSpace.wp

theorem jsoncodec.Next.wp [jsoncodec.Assumptions] :
    jsoncodec.Next.spec (GF := GF) (hG := hG) :=
  jsoncodec.Next.wp_proof jsoncodec.SkipSpace.wp

theorem jsoncodec.Empty.wp [jsoncodec.Assumptions] :
    jsoncodec.Empty.spec (GF := GF) (hG := hG) :=
  jsoncodec.Empty.wp_proof jsoncodec.SkipSpace.wp

theorem jsoncodec.Str.wp [jsoncodec.Assumptions] :
    jsoncodec.Str.spec (GF := GF) (hG := hG) :=
  jsoncodec.Str.wp_proof

theorem jsoncodec.Member.wp [jsoncodec.Assumptions] :
    jsoncodec.Member.spec (GF := GF) (hG := hG) :=
  jsoncodec.Member.wp_proof jsoncodec.SkipSpace.wp jsoncodec.Str.wp

theorem jsoncodec.Digits.wp [jsoncodec.Assumptions] :
    jsoncodec.Digits.spec (GF := GF) (hG := hG) :=
  jsoncodec.Digits.wp_proof

theorem jsoncodec.Uint.wp [jsoncodec.Assumptions] :
    jsoncodec.Uint.spec (GF := GF) (hG := hG) :=
  jsoncodec.Uint.wp_proof jsoncodec.At.wp jsoncodec.ValueEnd.wp jsoncodec.Digits.wp

theorem jsoncodec.QuotedUint.wp [jsoncodec.Assumptions] :
    jsoncodec.QuotedUint.spec (GF := GF) (hG := hG) :=
  jsoncodec.QuotedUint.wp_proof jsoncodec.At.wp jsoncodec.ValueEnd.wp jsoncodec.Digits.wp

theorem jsoncodec.String.wp [jsoncodec.Assumptions] :
    jsoncodec.String.spec (GF := GF) (hG := hG) :=
  jsoncodec.String.wp_proof jsoncodec.At.wp jsoncodec.Str.wp

theorem jsoncodec.AppendUint.wp [jsoncodec.Assumptions] :
    jsoncodec.AppendUint.spec (GF := GF) (hG := hG) :=
  jsoncodec.AppendUint.wp_proof

theorem jsoncodec.AppendQuotedUint.wp [jsoncodec.Assumptions] :
    jsoncodec.AppendQuotedUint.spec (GF := GF) (hG := hG) :=
  jsoncodec.AppendQuotedUint.wp_proof jsoncodec.AppendUint.wp

theorem jsoncodec.AppendString.wp [jsoncodec.Assumptions] :
    jsoncodec.AppendString.spec (GF := GF) (hG := hG) :=
  jsoncodec.AppendString.wp_proof

theorem jsoncodec.Valid.wp [jsoncodec.Assumptions] :
    jsoncodec.Valid.spec (GF := GF) (hG := hG) :=
  jsoncodec.Valid.wp_proof jsoncodec.Scan.wp jsoncodec.SkipSpace.wp

/-- `jsoncodec.Scan` computes `JsonScan.scanF` (`jsoncodec.scanOk_of`, linked). -/
theorem jsoncodec.scanOk_scanF [jsoncodec.Assumptions] :
    ⊢ jsoncodec.scanOk (GF := GF) JsonScan.scanF jsoncodec.scanFn :=
  jsoncodec.scanOk_of jsoncodec.Scan.wp

theorem pbcodec.Error.Error.wp [pbcodec.Assumptions] :
    pbcodec.Error.Error.spec (GF := GF) (hG := hG) :=
  pbcodec.Error.Error.wp_proof

/-- A kept `*jsoncodec.Error` is some error (`jsoncodec.Error_errAny`, linked). -/
theorem jsoncodec.Error_errAny' [jsoncodec.Assumptions] (e : Loc) (v : jsoncodec.Error) :
    (e ↦□ v : IProp GF) ⊢
      errAny (interface.mkOk (go.GoType.PointerType jsoncodec.Error.ty) #e) :=
  jsoncodec.Error_errAny jsoncodec.Error.Error.wp_proof e v

/-- A kept `*pbcodec.Error` is some error (`pbcodec.Error_errAny`, linked). -/
theorem pbcodec.Error_errAny' [pbcodec.Assumptions] (e : Loc) (v : pbcodec.Error) :
    (e ↦□ v : IProp GF) ⊢
      errAny (interface.mkOk (go.GoType.PointerType pbcodec.Error.ty) #e) :=
  pbcodec.Error_errAny pbcodec.Error.Error.wp_proof e v

end results

end models_lab
end Perennial

#print axioms Perennial.models_lab.jsoncodec.IsSpace.wp
#print axioms Perennial.models_lab.jsoncodec.AppendRaw.wp
#print axioms Perennial.models_lab.jsoncodec.AppendBool.wp
#print axioms Perennial.models_lab.jsoncodec.Error.Error.wp
#print axioms Perennial.models_lab.jsoncodec.Error_errAny'
#print axioms Perennial.models_lab.jsoncodec.SkipSpace.wp
#print axioms Perennial.models_lab.jsoncodec.Scan.wp
#print axioms Perennial.models_lab.jsoncodec.scanOk_scanF
#print axioms Perennial.models_lab.jsoncodec.Valid.wp
#print axioms Perennial.models_lab.jsoncodec.AppendUint.wp
#print axioms Perennial.models_lab.jsoncodec.AppendQuotedUint.wp
#print axioms Perennial.models_lab.jsoncodec.AppendString.wp
#print axioms Perennial.models_lab.jsoncodec.ValueEnd.wp
#print axioms Perennial.models_lab.jsoncodec.At.wp
#print axioms Perennial.models_lab.jsoncodec.Next.wp
#print axioms Perennial.models_lab.jsoncodec.Empty.wp
#print axioms Perennial.models_lab.jsoncodec.Str.wp
#print axioms Perennial.models_lab.jsoncodec.Member.wp
#print axioms Perennial.models_lab.jsoncodec.Digits.wp
#print axioms Perennial.models_lab.jsoncodec.Uint.wp
#print axioms Perennial.models_lab.jsoncodec.QuotedUint.wp
#print axioms Perennial.models_lab.jsoncodec.String.wp
#print axioms Perennial.models_lab.jsoncodec.wp_initialize'
#print axioms Perennial.models_lab.pbcodec.Error.Error.wp
#print axioms Perennial.models_lab.pbcodec.Error_errAny'
#print axioms Perennial.models_lab.pbcodec.wp_initialize'
