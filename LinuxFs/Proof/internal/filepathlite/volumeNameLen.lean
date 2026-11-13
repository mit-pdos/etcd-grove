/-
Proof of `LinuxFs/Spec/internal/filepathlite/volumeNameLen.lean`. Lean-first.
-/
module

public import LinuxFs.Spec.internal.filepathlite.volumeNameLen

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

theorem filepathlite.volumeNameLen.wp_proof :
    filepathlite.volumeNameLen.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  try wp_auto
  iapply HΦ
  try itrivial

end proof

end EtcdGrove
end Perennial
