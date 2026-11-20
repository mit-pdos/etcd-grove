/-
**The recursion cluster `value.CompareUsingRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `value.CompareUsing`, `value.ListCompareUsing`, `value.MapCompareUsing` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ value.CompareUsingRec.specI`) and its other
callees' specs; `value.CompareUsingRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `value.CompareUsingRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.CompareUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.ListCompareUsing
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.MapCompareUsing

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

/-- `value.CompareUsing.spec` inside the logic (Löb's hypothesis of `value.CompareUsingRec`). -/
def value.CompareUsing.specI : IProp GF :=
  iprop(
  ∀ (al : value.Allocator) (a b : value.Value) (dq1 dq2 : DFrac) (x y : UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isAlloc al ∗ isValF a dq1 x ∗ isValF b dq2 y ∗
      ⌜UVal.mapLensOk x = true ∧ UVal.mapLensOk y = true⌝ }}
    (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.CompareUsing)) (Val #al)) (Val #a)) (Val #b))
  {{ (r : w64), RET #r; isAlloc al ∗ isValF a dq1 x ∗ isValF b dq2 y ∗
      ⌜r.toInt = UVal.compare x y⌝ }})

/-- `value.ListCompareUsing.spec` inside the logic (Löb's hypothesis of `value.CompareUsingRec`). -/
def value.ListCompareUsing.specI : IProp GF :=
  iprop(
  ∀ (al : value.Allocator) (l r : value.List') (xs ys : List UVal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isAlloc al ∗ isListV l xs ∗ isListV r ys ∗
      ⌜UVal.mapLensOk (.list xs) = true ∧ UVal.mapLensOk (.list ys) = true⌝ }}
    (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.ListCompareUsing)) (Val #al)) (Val #l)) (Val #r))
  {{ (c : w64), RET #c; isAlloc al ∗ ⌜c.toInt = UVal.compare (.list xs) (.list ys)⌝ }})

/-- `value.MapCompareUsing.spec` inside the logic (Löb's hypothesis of `value.CompareUsingRec`). -/
def value.MapCompareUsing.specI : IProp GF :=
  iprop(
  ∀ (al : value.Allocator) (lm rm : value.Map) (ol or_ : Option (List (GoString × UVal))),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isAlloc al ∗ isMapO lm ol ∗ isMapO rm or_ ∗
      ⌜UVal.mapLensOk (.map (kvsOrEmpty ol)) = true ∧ UVal.mapLensOk (.map (kvsOrEmpty or_)) = true⌝ }}
    (App (App (App (Val (@! _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.MapCompareUsing)) (Val #al)) (Val #lm)) (Val #rm))
  {{ (c : w64), RET #c; isAlloc al ∗
      ⌜c.toInt = UVal.compare (.map (kvsOrEmpty ol)) (.map (kvsOrEmpty or_))⌝ }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def value.CompareUsingRec.specI : IProp GF :=
  iprop(value.CompareUsing.specI ∧
    value.ListCompareUsing.specI ∧
    value.MapCompareUsing.specI)

/-- **Every member's spec** (what `value.CompareUsingRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev value.CompareUsingRec.spec : Prop :=
  value.CompareUsing.spec (GF := GF) ∧
  value.ListCompareUsing.spec (GF := GF) ∧
  value.MapCompareUsing.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
