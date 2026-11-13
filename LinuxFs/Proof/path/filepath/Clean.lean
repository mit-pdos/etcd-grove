/-
Proof of `LinuxFs/Spec/path/filepath/Clean.lean`. Lean-first.
-/
module

public import LinuxFs.Spec.path.filepath.Clean
public import LinuxFs.Spec.internal.filepathlite.Clean

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

theorem filepath.Clean.wp_proof
    (hX : filepathlite.Clean.spec (GF := GF) (hG := hG)) :
    filepath.Clean.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start
  try wp_auto
  wp_apply hX as %r %Hr
  try wp_auto
  iapply HΦ; ipureintro; exact Hr

end proof

end EtcdGrove
end Perennial
