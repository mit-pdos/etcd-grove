/-
Proof of `LinuxFs/Spec/path/filepath/IsAbs.lean`. Lean-first.
-/
module

public import LinuxFs.Spec.path.filepath.IsAbs
public import LinuxFs.Spec.internal.filepathlite.IsAbs

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
variable [package_sem : _root_.Perennial.path.filepath.Assumptions]

theorem filepath.IsAbs.wp_proof
    (hX : filepathlite.IsAbs.spec (GF := GF) (hG := hG)) :
    filepath.IsAbs.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start
  try wp_auto
  wp_apply hX
  try wp_auto
  iapply HΦ; try itrivial

end proof

end EtcdGrove
end Perennial
