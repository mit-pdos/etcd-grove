/-
`Conflicts.Equals(c2)` (value receiver): the model's `conflictsEquals` (same length, and pairwise
the same manager and an equal path, `Path.Equals`).

Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.Own

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : merge.Assumptions]

/-- See the file header. -/
abbrev merge.Conflicts.Equals.spec : Prop :=
  ∀ (s1 s2 : merge.Conflicts) (a b : List Conflict),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗ ownConflicts s1 a ∗ ownConflicts s2 b }}
    (App (Val (s1 @!! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.Conflicts.ty @!! go!"Equals")) (Val #s2))
  {{ RET #(conflictsEquals a b); True }}

end spec

end smd
end EtcdGrove
end Perennial
