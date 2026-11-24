/-
Proof of `Spec/slices/Concat.lean`: an instance of Perennial's proved `slices.Concat`
(mit-pdos/perennial#670). Lean-first (no Rocq counterpart).
-/
module

public import Spec.slices.Concat
public import Perennial.Spec.slices.Concat

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace slices

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.slices.Assumptions]

theorem Concat.wp_proof
    (wp_Concat : _root_.Perennial.slices.Concat.spec (GF := GF) (hG := hG)) :
    Concat.spec (GF := GF) (hG := hG) := by
  intro ss dq sls xss dq' hlen hsum
  wp_start as ⟨Hss, Hsls⟩
  wp_apply (wp_Concat (S := go.GoType.SliceType go.string) ss dq sls xss dq' hlen hsum)
    $$ [$Hss $Hsls] as %s' ⟨Hss, Hsls, Hs', Hcap, -⟩
  iapply HΦ
  iframe

end proof

end slices
end EtcdGrove
end Perennial
