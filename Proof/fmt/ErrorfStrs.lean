/-
The proof of `Spec/fmt/ErrorfStrs.lean`, over Perennial's model of `fmt.Errorf`
(`Perennial/TrustedCode/fmt.lean`: `errors.New(format)`, the arguments ignored), as
`fmt.ErrorfErrs.wp_proof`; the spec's header says why the model may be used for these arguments.
-/
module

public import Spec.fmt.ErrorfStrs
public import Perennial.Proof.errors.NewVar
public import Proof.errors.ErrorStringOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [_root_.Perennial.fmt.Assumptions] [_root_.Perennial.errors.Assumptions]

theorem fmt.ErrorfStrs.wp_proof :
    fmt.ErrorfStrs.spec (GF := GF) (hG := hG) := by
  intro format args_sl args dq
  wp_start as ⟨Hsl, Has⟩
  wp_apply _root_.Perennial.errors.wp_New_errorString as %x #Herr
  iapply HΦ
  iframe Hsl Has
  iapply errorString_errOk
  iexact Herr

end proof

end EtcdGrove
end Perennial
