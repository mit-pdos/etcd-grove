/-
`merge.Updater.addBackOwnedItemsForVersion`:
not proved yet (`sorry`): Draft of the `merge` package's per-function specs (notes/smd-plan.md,
"The call DAG"); proved in the stage's Prove step, after the freeze.
Callees in other packages, whose Draft specs are written beside this one and become hypotheses here
when they are linked: `typed.TypedValue.ToFieldSet`, `typed.TypedValue.Schema`,
`typed.TypedValue.TypeRef`, `fieldpath.Set.EnsureNamedFieldsAreMembers`, `fieldpath.Set.Union`,
`fieldpath.Set.Difference`, `typed.TypedValue.RemoveItems`.

Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__addBackOwnedItemsForVersion

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

theorem merge.Updater.addBackOwnedItemsForVersion.wp_proof :
    merge.Updater.addBackOwnedItemsForVersion.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
