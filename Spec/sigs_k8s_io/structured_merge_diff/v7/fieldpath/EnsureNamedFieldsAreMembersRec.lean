/-
**The recursion cluster `fieldpath.EnsureNamedFieldsAreMembersRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `fieldpath.Set.EnsureNamedFieldsAreMembers`, `fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ fieldpath.EnsureNamedFieldsAreMembersRec.specI`) and its other
callees' specs; `fieldpath.EnsureNamedFieldsAreMembersRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `fieldpath.EnsureNamedFieldsAreMembersRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__EnsureNamedFieldsAreMembers
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__EnsureNamedFieldsAreMembers

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

/-- `fieldpath.Set.EnsureNamedFieldsAreMembers.spec` inside the logic (Löb's hypothesis of `fieldpath.EnsureNamedFieldsAreMembersRec`). -/
def fieldpath.Set.EnsureNamedFieldsAreMembers.specI : IProp GF :=
  iprop(
  ∀ (p : Loc) (s : PathSet) (sc : Loc) (S : Schema) (tr : schema.TypeRef) (ty : Option TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isSet p s ∗ isSchema sc S ∗ isTypeRefOpt tr ty ∗ ⌜S.WF ∧ s.CardLt (2 ^ 63)⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set'.ty @!! go!"EnsureNamedFieldsAreMembers")) (Val #sc)) (Val #tr))
  {{ (r : Loc), RET #r; isSet r (ensureNamedOpt S ty s) }})

/-- `fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.spec` inside the logic (Löb's hypothesis of `fieldpath.EnsureNamedFieldsAreMembersRec`). -/
def fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.specI : IProp GF :=
  iprop(
  ∀ (l : Loc) (D : PathSet) (sc : Loc) (S : Schema) (tr : schema.TypeRef) (ty : Option TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isNodes l D ∗ isSchema sc S ∗ isTypeRefOpt tr ty ∗ ⌜S.WF ∧ D.CardLt (2 ^ 63)⌝ }}
    (App (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap.ty @!! go!"EnsureNamedFieldsAreMembers")) (Val #sc)) (Val #tr))
  {{ (r : Loc), RET #r; isNodes r (PathSet.deep (ensureNamedOpt S ty D)) }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def fieldpath.EnsureNamedFieldsAreMembersRec.specI : IProp GF :=
  iprop(fieldpath.Set.EnsureNamedFieldsAreMembers.specI ∧
    fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.specI)

/-- **Every member's spec** (what `fieldpath.EnsureNamedFieldsAreMembersRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev fieldpath.EnsureNamedFieldsAreMembersRec.spec : Prop :=
  fieldpath.Set.EnsureNamedFieldsAreMembers.spec (GF := GF) ∧
  fieldpath.SetNodeMap.EnsureNamedFieldsAreMembers.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
