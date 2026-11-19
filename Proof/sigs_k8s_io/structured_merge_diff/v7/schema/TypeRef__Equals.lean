/-
`schema.TypeRef.Equals`:
not proved yet (`sorry`): Draft of the `schema` package's per-function specs (notes/smd-plan.md,
"The call DAG"); proved in the stage's Prove step, after the freeze.
No callee hypothesis: the call `a.Inlined.Equals(&b.Inlined)` is on two zero atoms in the
scope (`isTypeRefOpt`), where `Atom.Equals` returns `true` without calling `List.Equals` or
`Map.Equals`; the proof unfolds that call's body, so that the recursion `TypeRef.Equals` ->
`Atom.Equals` -> `Map.Equals` -> `TypeRef.Equals` is not a cycle among the proofs' hypotheses.

Lean-first (2026-11-19).
-/
module

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

theorem schema.TypeRef.Equals.wp_proof :
    schema.TypeRef.Equals.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
