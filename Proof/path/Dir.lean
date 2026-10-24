/-
Proof of `Spec/path/Dir.lean`. Lean-first.
-/
module

public import Spec.path.Dir
public import Spec.path.Split
public import Spec.path.Clean

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.path.Assumptions]

theorem path.Dir.wp_proof (hSplit : path.Split.spec (GF := GF) (hG := hG))
    (hClean : path.Clean.spec (GF := GF) (hG := hG)) :
    path.Dir.spec (GF := GF) (hG := hG) := by
  intro p
  wp_start
  try wp_auto
  wp_apply hSplit p
  try wp_auto
  wp_apply hClean _ as %r %Hr
  try wp_auto
  iapply HΦ
  ipureintro; rw [Hr]; rfl

end proof

end EtcdGrove
end Perennial
