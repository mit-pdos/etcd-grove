/-
`fmt.Printf` for arguments whose `Error()`/`String()` Go calls: from Perennial's `fmt.wp_Printf`
(fmtmodel, 2026-11-20: Perennial's model formats and calls the arguments' methods as Go does; until
then an axiom here).
-/
module

public import Spec.fmt.Printf
public import Perennial.Proof.fmt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.fmt.Assumptions]

theorem fmt.Printf.wp_proof : fmt.Printf.spec (GF := GF) (hG := hG) := by
  intro format args_sl xs dq
  iintro %Φ ⟨#Hpkg, Hsl, Hok⟩ HΦ
  wp_apply (_root_.Perennial.fmt.wp_Printf format args_sl xs dq) $$ [$Hpkg $Hsl $Hok]
    as %n %err Hsl
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
