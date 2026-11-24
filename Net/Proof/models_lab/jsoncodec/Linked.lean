/-
The linked results of `models.lab/jsoncodec`'s encoders (#24 J2) and (dsv-vr, round 8/9) its
scanner `SkipSpace`, `Scan` (`JsonScan.scanF`; `scanOk_scanF`), decoding helpers `ValueEnd`, `At`,
`Next`, `Empty`, `Str`, `Member`, `Digits`, `Uint`, `QuotedUint`, `String` (at valid input),
`AppendQuotedUint`, `Valid` (on one complete value), `Nesting` and `AppendCompact` (round 9), apart from `Results.lean` so that
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
public import Net.Proof.models_lab.jsoncodec.IsSpace
public import Net.Proof.models_lab.jsoncodec.SkipSpace
public import Net.Proof.models_lab.jsoncodec.Scan
public import Net.Proof.models_lab.jsoncodec.ScanOk
public import Net.Proof.models_lab.jsoncodec.Valid
public import Net.Proof.models_lab.jsoncodec.Nesting
public import Net.Proof.models_lab.jsoncodec.AppendCompact
public import Net.Proof.models_lab.jsoncodec.AppendQuotedUint
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

theorem jsoncodec.AppendQuotedUint.wp [jsoncodec.Assumptions] :
    jsoncodec.AppendQuotedUint.spec (GF := GF) (hG := hG) :=
  jsoncodec.AppendQuotedUint.wp_proof jsoncodec.AppendUint.wp

theorem jsoncodec.Valid.wp [jsoncodec.Assumptions] :
    jsoncodec.Valid.spec (GF := GF) (hG := hG) :=
  jsoncodec.Valid.wp_proof jsoncodec.Scan.wp jsoncodec.SkipSpace.wp

/-- `jsoncodec.Scan` computes `JsonScan.scanF` (`jsoncodec.scanOk_of`, linked). -/
theorem jsoncodec.scanOk_scanF [jsoncodec.Assumptions] :
    ⊢ jsoncodec.scanOk (GF := GF) JsonScan.scanF jsoncodec.scanFn :=
  jsoncodec.scanOk_of jsoncodec.Scan.wp

theorem jsoncodec.Nesting.wp [jsoncodec.Assumptions] :
    jsoncodec.Nesting.spec (GF := GF) (hG := hG) :=
  jsoncodec.Nesting.wp_proof

theorem jsoncodec.AppendCompact.wp [jsoncodec.Assumptions] :
    jsoncodec.AppendCompact.spec (GF := GF) (hG := hG) :=
  jsoncodec.AppendCompact.wp_proof jsoncodec.Valid.wp jsoncodec.IsSpace.wp_proof
    jsoncodec.htmlByte.wp

end results

end models_lab
end Perennial
