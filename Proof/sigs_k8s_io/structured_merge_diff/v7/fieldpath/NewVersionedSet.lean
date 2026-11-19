/-
`fieldpath.NewVersionedSet`: builds the struct and converts it. Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewVersionedSet

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : merge.Assumptions]

theorem fieldpath.NewVersionedSet.wp_proof : fieldpath.NewVersionedSet.spec (GF := GF) := fun p ver b => by
  wp_start as #Hpkg
  wp_auto
  iapply HΦ
  itrivial

end proof

end smd
end EtcdGrove
end Perennial
