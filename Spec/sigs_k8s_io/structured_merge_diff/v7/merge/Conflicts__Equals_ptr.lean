/-
`Conflicts.Equals(c2)` called through a pointer to the receiver (as the driver's
`conflicts.Equals(...)` on a local variable): as `Conflicts.Equals`.

Lean-first (2026-11-19, notes/smd-plan.md).
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
abbrev merge.Conflicts.Equals_ptr.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (s1 s2 : merge.Conflicts) (a b : List (GoString × Path)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.merge ∗ p ↦{dq} s1 ∗ isConflicts s1 a ∗ isConflicts s2 b }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.merge.Conflicts.ty @!! go!"Equals")) (Val #s2))
  {{ (r : Bool), RET #r; ⌜r = true ↔ a = b⌝ ∗ p ↦{dq} s1 }}

end spec

end smd
end EtcdGrove
end Perennial
