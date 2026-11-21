/-
The proof of `Spec/fmt/ErrorfLeaf.lean`, over Perennial's model of `fmt.Errorf`
(`Perennial/TrustedCode/fmt.lean`: `errors.New(format)`, the arguments ignored), as
`fmt.ErrorfErrs.wp_proof`; the spec's header says why the model may be used for these arguments.
-/
module

public import Spec.fmt.ErrorfLeaf
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

theorem fmt.ErrorfLeaf.wp_proof :
    fmt.ErrorfLeaf.spec (GF := GF) (hG := hG) := by
  intro format args_sl xs dq
  wp_start as ⟨Hsl, -⟩
  wp_apply _root_.Perennial.errors.wp_New_errorString as %x #Herr
  iapply HΦ
  iframe Hsl
  isplitr
  · iapply errorString_errOk
    iexact Herr
  · ipureintro
    have h := (go.MethodSetIs.method_set_is
      (t := go.GoType.PointerType errors.errorString.ty) go!"Errors")
    simp only [go.methodSetLookup] at h
    simpa using h

end proof

end EtcdGrove
end Perennial
