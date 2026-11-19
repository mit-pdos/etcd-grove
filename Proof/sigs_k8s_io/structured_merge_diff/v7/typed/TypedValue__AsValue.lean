/-
`TypedValue.AsValue`: returns its `value` field. Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__AsValue

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

theorem typed.TypedValue.AsValue.wp_proof : typed.TypedValue.AsValue.spec (GF := GF) := fun tv => by
  wp_start as #Hpkg
  wp_auto
  iapply HΦ
  itrivial

end proof

end smd
end EtcdGrove
end Perennial
