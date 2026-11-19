/-
`value.MapEqualsUsing(a, lhs, rhs)`: two nil maps are equal, a nil and a non-nil one are not
(even an empty one), two non-nil maps are equal when their entries are.

Internal to `value` (PRINCIPLES, "Scope": may mirror its code).

Lean-first (2026-11-19, notes/smd-plan.md): Draft, the stage's per-package specs of `value`.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects

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
variable [package_sem : value.Assumptions]

/-- See the file header. -/
abbrev value.MapEqualsUsing.spec : Prop :=
  ∀ (al : value.Allocator) (lm rm : value.Map) (ol or_ : Option (List (GoString × UVal))),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isAlloc al ∗ isMapO lm ol ∗ isMapO rm or_ }}
    (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.MapEqualsUsing)) (Val #al)) (Val #lm)) (Val #rm))
  {{ (b : Bool), RET #b; isAlloc al ∗ ⌜b = true ↔ ol = or_⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
