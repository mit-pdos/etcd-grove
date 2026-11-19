/-
**The recursion cluster `fieldpath.EmptyRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `fieldpath.Set.Empty`, `fieldpath.SetNodeMap.Empty` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ fieldpath.EmptyRec.specI`) and its other
callees' specs; `fieldpath.EmptyRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `fieldpath.EmptyRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Empty

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

/-- `fieldpath.Set.Empty.spec` inside the logic (Löb's hypothesis of `fieldpath.EmptyRec`). -/
def fieldpath.Set.Empty.specI : IProp GF :=
  iprop(
  ∀ (p : Loc) (S : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isSet p S }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set'.ty @!! go!"Empty")) (Val #()))
  {{ (r : Bool), RET #r; ⌜r = true ↔ S.IsEmpty⌝ }})

/-- `fieldpath.SetNodeMap.Empty.spec` inside the logic (Löb's hypothesis of `fieldpath.EmptyRec`). -/
def fieldpath.SetNodeMap.Empty.specI : IProp GF :=
  iprop(
  ∀ (l : Loc) (D : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isNodes l D }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap.ty @!! go!"Empty")) (Val #()))
  {{ (r : Bool), RET #r; ⌜r = true ↔ D.IsEmpty⌝ }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def fieldpath.EmptyRec.specI : IProp GF :=
  iprop(fieldpath.Set.Empty.specI ∧
    fieldpath.SetNodeMap.Empty.specI)

/-- **Every member's spec** (what `fieldpath.EmptyRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev fieldpath.EmptyRec.spec : Prop :=
  fieldpath.Set.Empty.spec (GF := GF) ∧
  fieldpath.SetNodeMap.Empty.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
