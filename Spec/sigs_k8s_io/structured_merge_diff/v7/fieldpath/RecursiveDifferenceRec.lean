/-
**The recursion cluster `fieldpath.RecursiveDifferenceRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `fieldpath.Set.RecursiveDifference`, `fieldpath.SetNodeMap.RecursiveDifference` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ fieldpath.RecursiveDifferenceRec.specI`) and its other
callees' specs; `fieldpath.RecursiveDifferenceRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `fieldpath.RecursiveDifferenceRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__RecursiveDifference
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__RecursiveDifference

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
variable [package_sem : fieldpath.Assumptions]

/-- `fieldpath.Set.RecursiveDifference.spec` inside the logic (Löb's hypothesis of `fieldpath.RecursiveDifferenceRec`). -/
def fieldpath.Set.RecursiveDifference.specI : IProp GF :=
  iprop(
  ∀ (p p2 : Loc) (A B : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isSet p A ∗ isSet p2 B }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set'.ty @!! go!"RecursiveDifference")) (Val #p2))
  {{ (r : Loc), RET #r; isSet r (PathSet.rdiff A B) }})

/-- `fieldpath.SetNodeMap.RecursiveDifference.spec` inside the logic (Löb's hypothesis of `fieldpath.RecursiveDifferenceRec`). -/
def fieldpath.SetNodeMap.RecursiveDifference.specI : IProp GF :=
  iprop(
  ∀ (l p2 : Loc) (D B : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isNodes l D ∗ isSet p2 B }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap.ty @!! go!"RecursiveDifference")) (Val #p2))
  {{ (r : Loc), RET #r; isNodes r (PathSet.rdiff D B) }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def fieldpath.RecursiveDifferenceRec.specI : IProp GF :=
  iprop(fieldpath.Set.RecursiveDifference.specI ∧
    fieldpath.SetNodeMap.RecursiveDifference.specI)

/-- **Every member's spec** (what `fieldpath.RecursiveDifferenceRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev fieldpath.RecursiveDifferenceRec.spec : Prop :=
  fieldpath.Set.RecursiveDifference.spec (GF := GF) ∧
  fieldpath.SetNodeMap.RecursiveDifference.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
