/-
Proof of `Spec/slices/Clone.lean`: an instance of Perennial's proved `slices.Clone`
(mit-pdos/perennial#670). Lean-first (no Rocq counterpart).
-/
module

public import Spec.slices.Clone
public import Perennial.Spec.slices.Clone

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

theorem Clone.wp_proof
    (wp_Clone : _root_.Perennial.slices.Clone.spec (GF := GF) (hG := hG)) :
    Clone.spec (GF := GF) (hG := hG) := by
  intro V _ _ E _ s dq xs
  wp_start as Hs
  wp_apply (wp_Clone (S := go.GoType.SliceType E)) $$ [$Hs] as %s' ⟨Hs, Hs', Hcap, -⟩
  iapply HΦ
  iframe

end proof

end slices
end EtcdGrove
end Perennial
