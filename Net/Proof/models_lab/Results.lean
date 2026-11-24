/-
The results of `models.lab`'s codec helpers (`models/`, project models; phase 5 item 1 of
notes/dsverify-net-port-plan.md), restated, with `#print axioms` of each (none beyond Lean's):

* `jsoncodec`: `IsSpace`, `AppendRaw`, `AppendBool`, `AppendString` (with `appendEscapedASCII`,
  `htmlByte`, `seqLen`, `seqLenOf`), `AppendUint`, `(*Error).Error`, and its package
  initialization; `Error_errAny` (a kept `*jsoncodec.Error` is some error);
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
public import Net.Proof.models_lab.jsoncodec.htmlByte
public import Net.Proof.models_lab.jsoncodec.appendEscapedASCII
public import Net.Proof.models_lab.jsoncodec.seqLenOf
public import Net.Proof.models_lab.jsoncodec.seqLen
public import Net.Proof.models_lab.jsoncodec.AppendString
public import Net.Proof.models_lab.jsoncodec.AppendUint
public import Net.Proof.models_lab.jsoncodec.Error__Error
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

theorem jsoncodec.htmlByte.wp [jsoncodec.Assumptions] :
    jsoncodec.htmlByte.spec (GF := GF) (hG := hG) :=
  jsoncodec.htmlByte.wp_proof

theorem jsoncodec.appendEscapedASCII.wp [jsoncodec.Assumptions] :
    jsoncodec.appendEscapedASCII.spec (GF := GF) (hG := hG) :=
  jsoncodec.appendEscapedASCII.wp_proof jsoncodec.htmlByte.wp

theorem jsoncodec.seqLenOf.wp [jsoncodec.Assumptions] :
    jsoncodec.seqLenOf.spec (GF := GF) (hG := hG) :=
  jsoncodec.seqLenOf.wp_proof

theorem jsoncodec.seqLen.wp [jsoncodec.Assumptions] :
    jsoncodec.seqLen.spec (GF := GF) (hG := hG) :=
  jsoncodec.seqLen.wp_proof jsoncodec.seqLenOf.wp

theorem jsoncodec.AppendString.wp [jsoncodec.Assumptions] :
    jsoncodec.AppendString.spec (GF := GF) (hG := hG) :=
  jsoncodec.AppendString.wp_proof jsoncodec.appendEscapedASCII.wp jsoncodec.seqLen.wp

theorem jsoncodec.AppendUint.wp [jsoncodec.Assumptions] :
    jsoncodec.AppendUint.spec (GF := GF) (hG := hG) :=
  jsoncodec.AppendUint.wp_proof

theorem jsoncodec.Error.Error.wp [jsoncodec.Assumptions] :
    jsoncodec.Error.Error.spec (GF := GF) (hG := hG) :=
  jsoncodec.Error.Error.wp_proof

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
#print axioms Perennial.models_lab.jsoncodec.htmlByte.wp
#print axioms Perennial.models_lab.jsoncodec.appendEscapedASCII.wp
#print axioms Perennial.models_lab.jsoncodec.seqLenOf.wp
#print axioms Perennial.models_lab.jsoncodec.seqLen.wp
#print axioms Perennial.models_lab.jsoncodec.AppendString.wp
#print axioms Perennial.models_lab.jsoncodec.AppendUint.wp
#print axioms Perennial.models_lab.jsoncodec.AppendBool.wp
#print axioms Perennial.models_lab.jsoncodec.Error.Error.wp
#print axioms Perennial.models_lab.jsoncodec.Error_errAny'
#print axioms Perennial.models_lab.jsoncodec.wp_initialize'
#print axioms Perennial.models_lab.pbcodec.Error.Error.wp
#print axioms Perennial.models_lab.pbcodec.Error_errAny'
#print axioms Perennial.models_lab.pbcodec.wp_initialize'
