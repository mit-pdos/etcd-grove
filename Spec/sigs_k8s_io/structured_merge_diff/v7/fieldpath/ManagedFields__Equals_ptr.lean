/-
`ManagedFields.Equals(rhs)` called through a pointer to the receiver (as the driver's
`s.managers.Equals(...)`): as `ManagedFields.Equals`.

Lean-first (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs

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
abbrev fieldpath.ManagedFields.Equals_ptr.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (m1 m2 : fieldpath.ManagedFields) (a b : MF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ p ↦{dq} m1 ∗ isMF m1 a ∗ isMF m2 b }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.ManagedFields.ty @!! go!"Equals")) (Val #m2))
  {{ (r : Bool), RET #r; ⌜r = true ↔ a = b⌝ ∗ p ↦{dq} m1 }}

end spec

end smd
end EtcdGrove
end Perennial
