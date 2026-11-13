/-
Proof of `LinuxFs/Spec/internal/filepathlite/IsPathSeparator.lean`. Lean-first.
-/
module

public import LinuxFs.Spec.internal.filepathlite.IsPathSeparator

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.internal.filepathlite.Assumptions]

theorem filepathlite.IsPathSeparator.wp_proof :
    filepathlite.IsPathSeparator.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  try wp_auto
  rw [show decide (W8 47 = x) = decide (x = W8 47) from decide_eq_decide.mpr eq_comm]
  iapply HΦ
  try itrivial

end proof

end EtcdGrove
end Perennial
