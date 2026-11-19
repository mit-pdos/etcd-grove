/-
**The recursion cluster `fieldpath.IntersectionRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `fieldpath.Set.Intersection`, `fieldpath.SetNodeMap.Intersection` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ fieldpath.IntersectionRec.specI`) and its other
callees' specs; `fieldpath.IntersectionRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `fieldpath.IntersectionRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Intersection
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Intersection

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

/-- `fieldpath.Set.Intersection.spec` inside the logic (Löb's hypothesis of `fieldpath.IntersectionRec`). -/
def fieldpath.Set.Intersection.specI : IProp GF :=
  iprop(
  ∀ (p p2 : Loc) (A B : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isSet p A ∗ isSet p2 B }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set'.ty @!! go!"Intersection")) (Val #p2))
  {{ (r : Loc), RET #r; isSet r (PathSet.inter A B) }})

/-- `fieldpath.SetNodeMap.Intersection.spec` inside the logic (Löb's hypothesis of `fieldpath.IntersectionRec`). -/
def fieldpath.SetNodeMap.Intersection.specI : IProp GF :=
  iprop(
  ∀ (l l2 : Loc) (D1 D2 : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isNodes l D1 ∗ isNodes l2 D2 }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap.ty @!! go!"Intersection")) (Val #l2))
  {{ (r : Loc), RET #r; isNodes r (PathSet.inter D1 D2) }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def fieldpath.IntersectionRec.specI : IProp GF :=
  iprop(fieldpath.Set.Intersection.specI ∧
    fieldpath.SetNodeMap.Intersection.specI)

/-- **Every member's spec** (what `fieldpath.IntersectionRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev fieldpath.IntersectionRec.spec : Prop :=
  fieldpath.Set.Intersection.spec (GF := GF) ∧
  fieldpath.SetNodeMap.Intersection.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
