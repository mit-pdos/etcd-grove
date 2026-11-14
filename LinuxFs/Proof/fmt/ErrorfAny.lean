/-
The proof of `LinuxFs/Spec/fmt/ErrorfAny.lean`, over Perennial's model of `fmt.Errorf`
(`Perennial/TrustedCode/fmt.lean`: `errors.New(format)`, the arguments ignored), as
`fmt.ErrorfErrs.wp_proof` is; why the model may be used for these arguments is the spec's header.
(2026-11-14.)
-/
module

public import LinuxFs.Spec.fmt.ErrorfAny
public import Perennial.Spec.errors.New

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

theorem fmt.ErrorfAny.wp_proof
    (wp_New : _root_.Perennial.errors.New.spec (GF := GF) (hG := hG)) :
    fmt.ErrorfAny.spec (GF := GF) (hG := hG) := by
  intro format args_sl args dq
  wp_start as Hsl
  wp_apply wp_New as %err -
  iapply HΦ
  iframe
  ipureintro; nofun

end proof

end EtcdGrove
end Perennial
