/-
Proof of `LinuxFs/Spec/internal/filepathlite/FromSlash.lean`. Lean-first.
-/
module

public import LinuxFs.Spec.internal.filepathlite.FromSlash

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

theorem filepathlite.FromSlash.wp_proof [go.IsStrictlyComparable go.untypedInt Int] :
    filepathlite.FromSlash.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  simp only [_root_.Perennial.internal.filepathlite.Separator]
  try wp_auto
  iapply HΦ
  try itrivial

end proof

end EtcdGrove
end Perennial
