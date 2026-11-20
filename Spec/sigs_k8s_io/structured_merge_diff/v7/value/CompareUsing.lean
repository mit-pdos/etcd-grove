/-
`value.CompareUsing(a, lhs, rhs)`: as `Compare`, over the allocator `a` (threaded: the
list and map cases allocate ranges and wrappers from it and free them). No floats in scope:
the float branches are dead.

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
abbrev value.CompareUsing.spec : Prop :=
  ∀ (al : value.Allocator) (a b : value.Value) (dq1 dq2 : DFrac) (x y : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isAlloc al ∗ isValF a dq1 x ∗ isValF b dq2 y ∗
      ⌜UVal.mapLensOk x = true ∧ UVal.mapLensOk y = true⌝ }}
    (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.CompareUsing)) (Val #al)) (Val #a)) (Val #b))
  {{ (r : w64), RET #r; isAlloc al ∗ isValF a dq1 x ∗ isValF b dq2 y ∗
      ⌜r.toInt = UVal.compare x y⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
