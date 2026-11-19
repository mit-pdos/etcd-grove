/-
**The recursion cluster `fieldpath.DifferenceRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `fieldpath.Set.Difference`, `fieldpath.SetNodeMap.Difference` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ fieldpath.DifferenceRec.specI`) and its other
callees' specs; `fieldpath.DifferenceRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `fieldpath.DifferenceRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Difference
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Difference

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

/-- `fieldpath.Set.Difference.spec` inside the logic (Löb's hypothesis of `fieldpath.DifferenceRec`). -/
def fieldpath.Set.Difference.specI : IProp GF :=
  iprop(
  ∀ (p p2 : Loc) (A B : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isSet p A ∗ isSet p2 B }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set'.ty @!! go!"Difference")) (Val #p2))
  {{ (r : Loc), RET #r; isSet r (PathSet.diff A B) }})

/-- `fieldpath.SetNodeMap.Difference.spec` inside the logic (Löb's hypothesis of `fieldpath.DifferenceRec`). -/
def fieldpath.SetNodeMap.Difference.specI : IProp GF :=
  iprop(
  ∀ (l p2 : Loc) (D B : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isNodes l D ∗ isSet p2 B }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap.ty @!! go!"Difference")) (Val #p2))
  {{ (r : Loc), RET #r; isNodes r (PathSet.diff D B) }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def fieldpath.DifferenceRec.specI : IProp GF :=
  iprop(fieldpath.Set.Difference.specI ∧
    fieldpath.SetNodeMap.Difference.specI)

/-- **Every member's spec** (what `fieldpath.DifferenceRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev fieldpath.DifferenceRec.spec : Prop :=
  fieldpath.Set.Difference.spec (GF := GF) ∧
  fieldpath.SetNodeMap.Difference.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
