/-
`Conflict.Equals(c2)` (value receiver): whether two conflicts have the same manager and equal
paths (`Path.Equals`): decides the equality of the (manager, path) pairs.

Internal to `merge` (its caller is `Conflicts.Equals`). Draft (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Defs

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
abbrev merge.Conflict.Equals.spec : Prop :=
  ∀ (c c2 : merge.Conflict) (a b : GoString × Path),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗ isConflict c a ∗ isConflict c2 b }}
    (App (Val (c @!! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.Conflict.ty @!! go!"Equals")) (Val #c2))
  {{ (r : Bool), RET #r; ⌜r = true ↔ a = b⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
