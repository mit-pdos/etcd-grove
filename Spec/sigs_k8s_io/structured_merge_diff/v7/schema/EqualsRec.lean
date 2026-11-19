/-
**The recursion cluster `schema.EqualsRec`** (the Draft's integration, 2026-11-19; `notes/smd-plan.md`,
"Draft integrated"): `schema.Atom.Equals`, `schema.List.Equals`, `schema.Map.Equals`, `schema.StructField.Equals`, `schema.TypeRef.Equals` call each other. The link (one proof per
function, callees' specs as hypotheses) is acyclic, so the cluster is proved together: each
member's body (`<member>.wp_proofBody`, its own `…Body.lean`) proves its spec inside the logic
(`<member>.specI`) from the cluster's specs under a later (`▷ schema.EqualsRec.specI`) and its other
callees' specs; `schema.EqualsRec.wp_proof` combines the bodies by Löb induction; each member's
`wp_proof` is the projection of `schema.EqualsRec.spec`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Atom__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.List__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.StructField__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.TypeRef__Equals

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
variable [package_sem : schema.Assumptions]

/-- `schema.Atom.Equals.spec` inside the logic (Löb's hypothesis of `schema.EqualsRec`). -/
def schema.Atom.Equals.specI : IProp GF :=
  iprop(
  ∀ (a b : Loc) (dq1 dq2 : DFrac) (va vb : schema.Atom) (oA oB : Option Atom),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.schema ∗ a ↦{dq1} va ∗ isAtomOpt va oA ∗ b ↦{dq2} vb ∗ isAtomOpt vb oB }}
    (App (Val (a @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.schema.Atom.ty @!! go!"Equals")) (Val #b))
  {{ (r : Bool), RET #r; a ↦{dq1} va ∗ b ↦{dq2} vb ∗ ⌜r = true ↔ oA = oB⌝ }})

/-- `schema.List.Equals.spec` inside the logic (Löb's hypothesis of `schema.EqualsRec`). -/
def schema.List.Equals.specI : IProp GF :=
  iprop(
  ∀ (a b : Loc) (e e' : TypeRef) (rel rel' : ElemRel) (ks ks' : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.schema ∗ isListRep a e rel ks ∗ isListRep b e' rel' ks' }}
    (App (Val (a @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.schema.List'.ty @!! go!"Equals")) (Val #b))
  {{ (r : Bool), RET #r; ⌜r = true ↔ (e, rel, ks) = (e', rel', ks')⌝ }})

/-- `schema.Map.Equals.spec` inside the logic (Löb's hypothesis of `schema.EqualsRec`). -/
def schema.Map.Equals.specI : IProp GF :=
  iprop(
  ∀ (a b : Loc) (fs fs' : List (GoString × TypeRef)) (e e' : Option TypeRef) (rel rel' : ElemRel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.schema ∗ isMapRep a fs e rel ∗ isMapRep b fs' e' rel' }}
    (App (Val (a @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.schema.Map.ty @!! go!"Equals")) (Val #b))
  {{ (r : Bool), RET #r; ⌜r = true ↔ (fs, e, rel) = (fs', e', rel')⌝ }})

/-- `schema.StructField.Equals.spec` inside the logic (Löb's hypothesis of `schema.EqualsRec`). -/
def schema.StructField.Equals.specI : IProp GF :=
  iprop(
  ∀ (a b : Loc) (dq1 dq2 : DFrac) (sa sb : schema.StructField) (f g : GoString × TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.schema ∗ a ↦{dq1} sa ∗ isStructField sa f ∗ b ↦{dq2} sb ∗ isStructField sb g }}
    (App (Val (a @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.schema.StructField.ty @!! go!"Equals")) (Val #b))
  {{ (r : Bool), RET #r; a ↦{dq1} sa ∗ b ↦{dq2} sb ∗ ⌜r = true ↔ f = g⌝ }})

/-- `schema.TypeRef.Equals.spec` inside the logic (Löb's hypothesis of `schema.EqualsRec`). -/
def schema.TypeRef.Equals.specI : IProp GF :=
  iprop(
  ∀ (a b : Loc) (dq1 dq2 : DFrac) (ta tb : schema.TypeRef) (oa ob : Option TypeRef),
  {{ isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.schema ∗ a ↦{dq1} ta ∗ isTypeRefOpt ta oa ∗ b ↦{dq2} tb ∗ isTypeRefOpt tb ob }}
    (App (Val (a @!! go.GoType.PointerType _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.schema.TypeRef.ty @!! go!"Equals")) (Val #b))
  {{ (r : Bool), RET #r; a ↦{dq1} ta ∗ b ↦{dq2} tb ∗ ⌜r = true ↔ oa = ob⌝ }})

/-- **The cluster's specs inside the logic**: what each member's body assumes under a later
(`<member>.specBody`), and what Löb's induction proves. -/
def schema.EqualsRec.specI : IProp GF :=
  iprop(schema.Atom.Equals.specI ∧
    schema.List.Equals.specI ∧
    schema.Map.Equals.specI ∧
    schema.StructField.Equals.specI ∧
    schema.TypeRef.Equals.specI)

/-- **Every member's spec** (what `schema.EqualsRec.wp_proof` proves; each member's `wp_proof` is its
projection). -/
abbrev schema.EqualsRec.spec : Prop :=
  schema.Atom.Equals.spec (GF := GF) ∧
  schema.List.Equals.spec (GF := GF) ∧
  schema.Map.Equals.spec (GF := GF) ∧
  schema.StructField.Equals.spec (GF := GF) ∧
  schema.TypeRef.Equals.spec (GF := GF)

end spec

end smd
end EtcdGrove
end Perennial
