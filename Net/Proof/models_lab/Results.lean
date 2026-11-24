/-
The results of `models.lab`'s codec helpers (`models/`, project models; phase 5 item 1 of
notes/dsverify-net-port-plan.md), restated, with `#print axioms` of each (none beyond Lean's):

* `jsoncodec`: `IsSpace`, `AppendRaw`, `AppendBool`, `AppendString` (with `appendEscapedASCII`,
  `htmlByte`, `seqLen`, `seqLenOf`), `AppendUint`, `(*Error).Error`, and its package
  initialization; `Error_errAny` (a kept `*jsoncodec.Error` is some error);
* `pbcodec`: `(*Error).Error`, its package initialization, and `Error_errAny`; (#37 stage S3) the
  encoder's `SizeVarint`, `AppendVarint`, `AppendTag`, `AppendBytes`, against `Wire.lean`'s varints
  and records (what the protobuf model's generated methods call).

The codec obligations (`pbcodec.PbCodec`, `marshalOk`, `unmarshalOk`; `jsoncodec.JsonCodec`,
`jsonValid`, `marshalOk`, `unmarshalOk`, `scanOk`) are definitions, in `pbcodec/Codec.lean` and
`jsoncodec/Codec.lean`: each program proves them of its generated codec.
-/
module

public import Net.Proof.models_lab.pbcodec.Codec
public import Net.Proof.models_lab.pbcodec.Init
public import Net.Proof.models_lab.jsoncodec.Codec
public import Net.Proof.models_lab.jsoncodec.Init
public import Net.Proof.models_lab.jsoncodec.Linked
public import Net.Proof.models_lab.jsoncodec.IsSpace
public import Net.Proof.models_lab.jsoncodec.Error__Error
public import Net.Proof.models_lab.pbcodec.Error__Error
public import Net.Proof.models_lab.pbcodec.SizeVarint
public import Net.Proof.models_lab.pbcodec.AppendVarint
public import Net.Proof.models_lab.pbcodec.AppendTag
public import Net.Proof.models_lab.pbcodec.AppendBytes

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

theorem jsoncodec.Error.Error.wp [jsoncodec.Assumptions] :
    jsoncodec.Error.Error.spec (GF := GF) (hG := hG) :=
  jsoncodec.Error.Error.wp_proof

theorem pbcodec.Error.Error.wp [pbcodec.Assumptions] :
    pbcodec.Error.Error.spec (GF := GF) (hG := hG) :=
  pbcodec.Error.Error.wp_proof

theorem pbcodec.SizeVarint.wp [pbcodec.Assumptions] :
    pbcodec.SizeVarint.spec (GF := GF) (hG := hG) :=
  pbcodec.SizeVarint.wp_proof

theorem pbcodec.AppendVarint.wp [pbcodec.Assumptions] :
    pbcodec.AppendVarint.spec (GF := GF) (hG := hG) :=
  pbcodec.AppendVarint.wp_proof

theorem pbcodec.AppendTag.wp [pbcodec.Assumptions] :
    pbcodec.AppendTag.spec (GF := GF) (hG := hG) :=
  pbcodec.AppendTag.wp_proof pbcodec.AppendVarint.wp_proof

theorem pbcodec.AppendBytes.wp [pbcodec.Assumptions] :
    pbcodec.AppendBytes.spec (GF := GF) (hG := hG) :=
  pbcodec.AppendBytes.wp_proof pbcodec.AppendVarint.wp_proof

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
#print axioms Perennial.models_lab.pbcodec.SizeVarint.wp
#print axioms Perennial.models_lab.pbcodec.AppendVarint.wp
#print axioms Perennial.models_lab.pbcodec.AppendTag.wp
#print axioms Perennial.models_lab.pbcodec.AppendBytes.wp
