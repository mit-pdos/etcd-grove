/-
`merge.Updater.update`:
not proved yet (`sorry`): Draft of the `merge` package's per-function specs (notes/smd-plan.md,
"The call DAG"); proved in the stage's Prove step, after the freeze.
Callees in other packages, whose Draft specs are written beside this one and become hypotheses here
when they are linked: `typed.TypedValue.Compare`, `typed.Comparison.FilterFields`,
`fieldpath.versionedSet.Set`, `fieldpath.versionedSet.APIVersion`, `fieldpath.versionedSet.Applied`,
`fieldpath.Set.Union`, `fieldpath.Set.Intersection`, `fieldpath.Set.Difference`,
`fieldpath.Set.Empty`.

Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.Updater__update
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NewVersionedSet
public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.ConflictsFromManagers

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

theorem merge.Updater.update.wp_proof
    (hNewVersionedSet : fieldpath.NewVersionedSet.spec (GF := GF))
    (hConflictsFromManagers : merge.ConflictsFromManagers.spec (GF := GF)) :
    merge.Updater.update.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
