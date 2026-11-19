/-
`value.ListCompareUsing(a, lhs, rhs)`: the lexicographic order of two lists
(`UVal.compare` of the lists) (internal: `CompareUsing`'s list case).

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
abbrev value.ListCompareUsing.spec : Prop :=
  ∀ (al : value.Allocator) (l r : value.List') (xs ys : List UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isAlloc al ∗ isListV l xs ∗ isListV r ys }}
    (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.ListCompareUsing)) (Val #al)) (Val #l)) (Val #r))
  {{ (c : w64), RET #c; isAlloc al ∗ ⌜c.toInt = UVal.compare (.list xs) (.list ys)⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
