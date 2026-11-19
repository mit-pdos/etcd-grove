/-
**The recursion cluster `fieldpath.EqualsRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `fieldpath.Set.Equals`, `fieldpath.SetNodeMap.Equals` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ fieldpath.EqualsRec.specI`) and its other
callees' specs; `fieldpath.EqualsRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `fieldpath.EqualsRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Equals

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

/-- `fieldpath.Set.Equals.spec` inside the logic (Löb's hypothesis of `fieldpath.EqualsRec`). -/
def fieldpath.Set.Equals.specI : IProp GF :=
  iprop(
  ∀ (p p2 : Loc) (A B : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isSet p A ∗ isSet p2 B }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set'.ty @!! go!"Equals")) (Val #p2))
  {{ (r : Bool), RET #r; ⌜r = true ↔ A = B⌝ }})

/-- `fieldpath.SetNodeMap.Equals.spec` inside the logic (Löb's hypothesis of `fieldpath.EqualsRec`). -/
def fieldpath.SetNodeMap.Equals.specI : IProp GF :=
  iprop(
  ∀ (l l2 : Loc) (D1 D2 : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isNodes l D1 ∗ isNodes l2 D2 }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap.ty @!! go!"Equals")) (Val #l2))
  {{ (r : Bool), RET #r; ⌜r = true ↔ D1 = D2⌝ }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def fieldpath.EqualsRec.specI : IProp GF :=
  iprop(fieldpath.Set.Equals.specI ∧
    fieldpath.SetNodeMap.Equals.specI)

/-- **Every member's spec** (what `fieldpath.EqualsRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev fieldpath.EqualsRec.spec : Prop :=
  fieldpath.Set.Equals.spec (GF := GF) ∧
  fieldpath.SetNodeMap.Equals.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
