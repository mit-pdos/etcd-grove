/-
**The recursion cluster `fieldpath.UnionRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `fieldpath.Set.Union`, `fieldpath.SetNodeMap.Union` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ fieldpath.UnionRec.specI`) and its other
callees' specs; `fieldpath.UnionRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `fieldpath.UnionRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Union
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Union

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

/-- `fieldpath.Set.Union.spec` inside the logic (Löb's hypothesis of `fieldpath.UnionRec`). -/
def fieldpath.Set.Union.specI : IProp GF :=
  iprop(
  ∀ (p p2 : Loc) (A B : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isSet p A ∗ isSet p2 B }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set'.ty @!! go!"Union")) (Val #p2))
  {{ (r : Loc), RET #r; isSet r (PathSet.union A B) }})

/-- `fieldpath.SetNodeMap.Union.spec` inside the logic (Löb's hypothesis of `fieldpath.UnionRec`). -/
def fieldpath.SetNodeMap.Union.specI : IProp GF :=
  iprop(
  ∀ (l l2 : Loc) (D1 D2 : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isNodes l D1 ∗ isNodes l2 D2 }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap.ty @!! go!"Union")) (Val #l2))
  {{ (r : Loc), RET #r; isNodes r (PathSet.union D1 D2) }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def fieldpath.UnionRec.specI : IProp GF :=
  iprop(fieldpath.Set.Union.specI ∧
    fieldpath.SetNodeMap.Union.specI)

/-- **Every member's spec** (what `fieldpath.UnionRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev fieldpath.UnionRec.spec : Prop :=
  fieldpath.Set.Union.spec (GF := GF) ∧
  fieldpath.SetNodeMap.Union.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
