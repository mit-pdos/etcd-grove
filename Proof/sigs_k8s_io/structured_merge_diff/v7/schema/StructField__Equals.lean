/-
`schema.StructField.Equals`:
not proved yet (`sorry`): Draft of the `schema` package's per-function specs (notes/smd-plan.md,
"The call DAG"); proved in the stage's Prove step, after the freeze.

Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.StructField__Equals
public import Spec.reflect.DeepEqualNil
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.TypeRef__Equals

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
variable [package_sem : schema.Assumptions]

theorem schema.StructField.Equals.wp_proof
    (hDeepEqual : _root_.Perennial.EtcdGrove.reflect.DeepEqual.specNil (GF := GF) (hG := hG))
    (hTypeRefEquals : schema.TypeRef.Equals.spec (GF := GF)) :
    schema.StructField.Equals.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
