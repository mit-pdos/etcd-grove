/-
`fieldpath.FieldNameElement`: a path element pointing to a new cell holding the name, made
persistent. Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.FieldNameElement

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

theorem fieldpath.FieldNameElement.wp_proof : fieldpath.FieldNameElement.spec (GF := GF) := fun n => by
  wp_start as #Hpkg
  iapply wp_fupd
  wp_auto
  ipersist name
  imodintro
  iapply HΦ
  unfold isPE
  iexact name

end proof

end smd
end EtcdGrove
end Perennial
