/-
Proof of `LinuxFs/Spec/path/filepath/Abs.lean`. Lean-first.
-/
module

public import LinuxFs.Spec.path.filepath.Abs
public import LinuxFs.Spec.path.filepath.IsAbs
public import LinuxFs.Spec.path.filepath.Clean

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

theorem filepath.Abs.wp_proof
    (hIsAbs : filepath.IsAbs.spec (GF := GF) (hG := hG))
    (hClean : filepath.Clean.spec (GF := GF) (hG := hG)) :
    filepath.Abs.spec (GF := GF) (hG := hG) := by
  intro p hp
  wp_start
  try wp_auto
  wp_func_call
  wp_call
  try wp_auto
  wp_func_call
  wp_call
  try wp_auto
  wp_apply hIsAbs
  try wp_auto
  simp only [decide_eq_true hp]
  try wp_auto
  wp_apply hClean as %r %Hr
  try wp_auto
  subst Hr
  iapply HΦ; try itrivial

end proof

end EtcdGrove
end Perennial
