/-
`(*Conflicts).Equals(c2)`, called through a pointer to a `Conflicts` variable
(`conflicts.Equals(...)`): as `Conflicts.Equals` on the variable's slice.

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
abbrev merge.Conflicts.Equals_ptr.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (s1 s2 : merge.Conflicts) (a b : List Conflict),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗ p ↦{dq} s1 ∗ ownConflicts s1 a ∗ ownConflicts s2 b }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.Conflicts.ty @!! go!"Equals")) (Val #s2))
  {{ RET #(conflictsEquals a b); p ↦{dq} s1 }}

end spec

end smd
end EtcdGrove
end Perennial
