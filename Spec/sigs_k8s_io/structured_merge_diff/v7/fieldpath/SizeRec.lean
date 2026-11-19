/-
**The recursion cluster `fieldpath.SizeRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `fieldpath.Set.Size`, `fieldpath.SetNodeMap.Size` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ fieldpath.SizeRec.specI`) and its other
callees' specs; `fieldpath.SizeRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `fieldpath.SizeRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Size
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__Size

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

/-- `fieldpath.Set.Size.spec` inside the logic (Löb's hypothesis of `fieldpath.SizeRec`). -/
def fieldpath.Set.Size.specI : IProp GF :=
  iprop(
  ∀ (p : Loc) (S : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isSet p S }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set'.ty @!! go!"Size")) (Val #()))
  {{ (r : w64), RET #r; ⌜∀ n, S.HasCard n → n < 2 ^ 63 → sint.Z r = n⌝ }})

/-- `fieldpath.SetNodeMap.Size.spec` inside the logic (Löb's hypothesis of `fieldpath.SizeRec`). -/
def fieldpath.SetNodeMap.Size.specI : IProp GF :=
  iprop(
  ∀ (l : Loc) (D : PathSet),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isNodes l D }}
    (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap.ty @!! go!"Size")) (Val #()))
  {{ (r : w64), RET #r; ⌜∀ n, D.HasCard n → n < 2 ^ 63 → sint.Z r = n⌝ }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def fieldpath.SizeRec.specI : IProp GF :=
  iprop(fieldpath.Set.Size.specI ∧
    fieldpath.SetNodeMap.Size.specI)

/-- **Every member's spec** (what `fieldpath.SizeRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev fieldpath.SizeRec.spec : Prop :=
  fieldpath.Set.Size.spec (GF := GF) ∧
  fieldpath.SetNodeMap.Size.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
