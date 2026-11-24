/-
The linked results of `models.lab/jsoncodec`'s encoders (#24 J2), apart from `Results.lean` so that
a main-tree linking module (the server's `Link`, whose membership JSON proofs take them) imports
them without the part's package initializers (`Init`, Net's `PkgInitExt`).
-/
module

public import Net.Proof.models_lab.jsoncodec.htmlByte
public import Net.Proof.models_lab.jsoncodec.appendEscapedASCII
public import Net.Proof.models_lab.jsoncodec.seqLenOf
public import Net.Proof.models_lab.jsoncodec.seqLen
public import Net.Proof.models_lab.jsoncodec.AppendString
public import Net.Proof.models_lab.jsoncodec.AppendUint
public import Net.Proof.models_lab.jsoncodec.AppendRaw
public import Net.Proof.models_lab.jsoncodec.AppendBool

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

theorem jsoncodec.AppendRaw.wp [jsoncodec.Assumptions] :
    jsoncodec.AppendRaw.spec (GF := GF) (hG := hG) :=
  jsoncodec.AppendRaw.wp_proof

theorem jsoncodec.AppendBool.wp [jsoncodec.Assumptions] :
    jsoncodec.AppendBool.spec (GF := GF) (hG := hG) :=
  jsoncodec.AppendBool.wp_proof

end results

end models_lab
end Perennial
