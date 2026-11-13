/-
Proof of `LinuxFs/Spec/internal/filepathlite/VolumeName.lean`. Lean-first.
-/
module

public import LinuxFs.Spec.internal.filepathlite.VolumeName
public import LinuxFs.Spec.internal.filepathlite.volumeNameLen
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

theorem filepathlite.VolumeName.wp_proof
    (hVol : filepathlite.volumeNameLen.spec (GF := GF) (hG := hG))
    (hFrom : filepathlite.FromSlash.spec (GF := GF) (hG := hG)) :
    filepathlite.VolumeName.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  try wp_auto
  wp_apply hVol
  try wp_auto
  wp_apply hFrom
  try wp_auto
  simp only [Nat.sub_zero, List.take_zero]
  iapply HΦ
  try itrivial

end proof

end EtcdGrove
end Perennial
