/-
`value.MapCompareUsing(a, lhs, rhs)`: the order of two maps (`UVal.compare` of the maps; a
nil `Map` is empty) (internal: `CompareUsing`'s map case).

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
abbrev value.MapCompareUsing.spec : Prop :=
  ∀ (al : value.Allocator) (lm rm : value.Map) (ol or_ : Option (List (GoString × UVal))),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isAlloc al ∗ isMapO lm ol ∗ isMapO rm or_ ∗
      ⌜UVal.mapLensOk (.map (kvsOrEmpty ol)) = true ∧ UVal.mapLensOk (.map (kvsOrEmpty or_)) = true⌝ }}
    (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.MapCompareUsing)) (Val #al)) (Val #lm)) (Val #rm))
  {{ (c : w64), RET #c; isAlloc al ∗
      ⌜c.toInt = UVal.compare (.map (kvsOrEmpty ol)) (.map (kvsOrEmpty or_))⌝ }}

end spec

end smd
end EtcdGrove
end Perennial
