/-
`merge.ConflictsFromManagers`:
not proved yet (`sorry`): Draft of the `merge` package's per-function specs (notes/smd-plan.md,
"The call DAG"); proved in the stage's Prove step, after the freeze.
Callees in other packages, whose Draft specs are written beside this one and become hypotheses here
when they are linked: `fieldpath.versionedSet.Set`, `fieldpath.Set.Iterate`, `fieldpath.Path.Copy`.

Lean-first (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.merge.ConflictsFromManagers
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Path__Copy
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Iterate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.versionedSet__Set

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

theorem merge.ConflictsFromManagers.wp_proof
    (h_Path_Copy : fieldpath.Path.Copy.spec (GF := GF))
    (h_Set_Iterate : fieldpath.Set.Iterate.spec (GF := GF))
    (h_versionedSet_Set : fieldpath.versionedSet.Set.spec (GF := GF)) :
    merge.ConflictsFromManagers.spec (GF := GF) := by
  sorry

end proof

end smd
end EtcdGrove
end Perennial
