/-
**The recursion cluster `fieldpath.iteratePrefixRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `fieldpath.Set.iteratePrefix`, `fieldpath.SetNodeMap.iteratePrefix` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ fieldpath.iteratePrefixRec.specI`) and its other
callees' specs; `fieldpath.iteratePrefixRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `fieldpath.iteratePrefixRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__iteratePrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap__iteratePrefix

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

/-- `fieldpath.Set.iteratePrefix.spec` inside the logic (Löb's hypothesis of `fieldpath.iteratePrefixRec`). -/
def fieldpath.Set.iteratePrefix.specI : IProp GF :=
  iprop(
  ∀ (p : Loc) (S : PathSet) (ps : GoSlice) (es : List fieldpath.PathElement) (pre : Path)
    (f : GoFunc) (T : PathSet) (I : List Path → IProp GF) (done0 : List Path),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isSet p S ∗ ps ↦* es ∗ ownSliceCap fieldpath.PathElement ps (DFrac.own 1) ∗
      isPEs es pre ∗ I done0 ∗ ⌜∀ q, q ∈ S → (pre ++ q) ∈ T ∧ (pre ++ q) ∉ done0⌝ ∗
      □ (∀ (done : List Path) (q : Path) (s : GoSlice) (dq : DFrac), ⌜q ∈ T ∧ q ∉ done⌝ -∗
        {{ I done ∗ isPathF s dq q }} (App (Val #f) (Val #s))
        {{ RET #(); I (done ++ [q]) ∗ isPathF s dq q }}) }}
    (App (App (Val (p @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set'.ty @!! go!"iteratePrefix")) (Val #ps)) (Val #f))
  {{ RET #(); ps ↦* es ∗ ownSliceCap fieldpath.PathElement ps (DFrac.own 1) ∗
      ∃ ds : List Path, ⌜ds.Nodup ∧ FSet.ofList ds = PathSet.prepend pre S⌝ ∗ I (done0 ++ ds) }})

/-- `fieldpath.SetNodeMap.iteratePrefix.spec` inside the logic (Löb's hypothesis of `fieldpath.iteratePrefixRec`). -/
def fieldpath.SetNodeMap.iteratePrefix.specI : IProp GF :=
  iprop(
  ∀ (l : Loc) (D : PathSet) (ps : GoSlice) (es : List fieldpath.PathElement) (pre : Path)
    (f : GoFunc) (T : PathSet) (I : List Path → IProp GF) (done0 : List Path),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.fieldpath ∗ isNodes l D ∗ ps ↦* es ∗ ownSliceCap fieldpath.PathElement ps (DFrac.own 1) ∗
      isPEs es pre ∗ I done0 ∗ ⌜∀ q, q ∈ D → (pre ++ q) ∈ T ∧ (pre ++ q) ∉ done0⌝ ∗
      □ (∀ (done : List Path) (q : Path) (s : GoSlice) (dq : DFrac), ⌜q ∈ T ∧ q ∉ done⌝ -∗
        {{ I done ∗ isPathF s dq q }} (App (Val #f) (Val #s))
        {{ RET #(); I (done ++ [q]) ∗ isPathF s dq q }}) }}
    (App (App (Val (l @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.fieldpath.SetNodeMap.ty @!! go!"iteratePrefix")) (Val #ps)) (Val #f))
  {{ RET #(); ps ↦* es ∗ ownSliceCap fieldpath.PathElement ps (DFrac.own 1) ∗
      ∃ ds : List Path, ⌜ds.Nodup ∧ FSet.ofList ds = PathSet.prepend pre D⌝ ∗ I (done0 ++ ds) }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def fieldpath.iteratePrefixRec.specI : IProp GF :=
  iprop(fieldpath.Set.iteratePrefix.specI ∧
    fieldpath.SetNodeMap.iteratePrefix.specI)

/-- **Every member's spec** (what `fieldpath.iteratePrefixRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev fieldpath.iteratePrefixRec.spec : Prop :=
  fieldpath.Set.iteratePrefix.spec (GF := GF) ∧
  fieldpath.SetNodeMap.iteratePrefix.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
