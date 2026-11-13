/-
Proof of `LinuxFs/Spec/path/filepath/Join.lean`: `Join` is `join` (`path_unix.go`). Lean-first.
-/
module

public import LinuxFs.Spec.path.filepath.Join
public import LinuxFs.Spec.path.filepath.join

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

theorem filepath.Join.wp_proof (hjoin : filepath.join.spec (GF := GF) (hG := hG)) :
    filepath.Join.spec (GF := GF) (hG := hG) := by
  intro sl es dq _
  wp_start as Hsl
  try wp_auto
  wp_apply hjoin sl es dq $$ [Hsl] as %r ⟨%Hr, Hsl⟩
  · iframe
  try wp_auto
  iapply HΦ
  iframe
  ipureintro; exact Hr

end proof

end EtcdGrove
end Perennial
