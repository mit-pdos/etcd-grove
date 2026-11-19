/-
**The laws of the `schema` package's piece views** (`isAtomOpt`, `isListRep`, `isMapRep`,
`isStructField`, `isTypeRefOpt`; `schema/Defs.lean`) that the clients of `schema`'s
per-function specs need: `typed`'s walkers and `fieldpath`'s `EnsureNamedFieldsAreMembers` read an atom's fields
after `Resolve` (a scalar's name, a list's element type and keys, a map's element type and
relationship, and compare `ElementType` with `schema.TypeRef{}`), call `Map.FindField` on a map
type, and pass the empty `TypeRef` to `Resolve`. Stated, not proved (`def <name>.law : Prop`, as
`v7/Laws.lean`): the next phase's invariant work. They may move into `v7/Laws.lean`.

Draft (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ## Persistence -/

def isTypeRefOpt_persistent.law : Prop :=
  ∀ tr ot, isTypeRefOpt (GF := GF) tr ot ⊢ □ isTypeRefOpt tr ot
def isAtomOpt_persistent.law : Prop := ∀ a oA, isAtomOpt (GF := GF) a oA ⊢ □ isAtomOpt a oA
def isListRep_persistent.law : Prop :=
  ∀ l e rel ks, isListRep (GF := GF) l e rel ks ⊢ □ isListRep l e rel ks
def isMapRep_persistent.law : Prop :=
  ∀ m fs e rel, isMapRep (GF := GF) m fs e rel ⊢ □ isMapRep m fs e rel
def isStructField_persistent.law : Prop :=
  ∀ sf f, isStructField (GF := GF) sf f ⊢ □ isStructField sf f

/-! ## Type references -/

/-- A named reference is an `isTypeRefOpt` at `some`. -/
def isTypeRefOpt_some.law : Prop :=
  ∀ tr t, isTypeRefOpt (GF := GF) tr (some t) ⊣⊢ isTypeRef tr t

/-- The empty reference is exactly the zero `schema.TypeRef` (`schema.TypeRef{}`: what the walkers
resolve for a key without a type, and compare a map's `ElementType` with). -/
def isTypeRefOpt_none.law : Prop :=
  ∀ tr, isTypeRefOpt (GF := GF) tr none ⊣⊢ ⌜tr = zero_val schema.TypeRef⌝

/-- A named reference's fields (`*tr.NamedType` in error messages; `tr != schema.TypeRef{}`). -/
def isTypeRef_elim.law : Prop :=
  ∀ tr t, isTypeRef (GF := GF) tr t ⊢
    tr.NamedType' ↦□ t.name ∗
    ⌜tr.Inlined' = zero_val schema.Atom ∧ tr.ElementRelationship' = null ∧ tr.Nullable' = t.nullable⌝

/-! ## Atoms, lists, maps, fields (elimination: what a client reads) -/

/-- The zero atom: no kind set. -/
def isAtomOpt_none.law : Prop :=
  ∀ a, isAtomOpt (GF := GF) a none ⊣⊢ ⌜a = zero_val schema.Atom⌝

def isAtomOpt_scalar.law : Prop :=
  ∀ a s, isAtomOpt (GF := GF) a (some (.scalar s)) ⊣⊢
    a.Scalar' ↦□ s.goName ∗ ⌜a.List' = null ∧ a.Map' = null⌝

def isAtomOpt_list.law : Prop :=
  ∀ a e rel ks, isAtomOpt (GF := GF) a (some (.list e rel ks)) ⊣⊢
    ⌜a.Scalar' = null ∧ a.Map' = null⌝ ∗ isListRep a.List' e rel ks

def isAtomOpt_map.law : Prop :=
  ∀ a fs e rel, isAtomOpt (GF := GF) a (some (.map fs e rel)) ⊣⊢
    ⌜a.Scalar' = null ∧ a.List' = null⌝ ∗ isMapRep a.Map' fs e rel

/-- A list type's fields. -/
def isListRep_elim.law : Prop :=
  ∀ l e rel ks, isListRep (GF := GF) l e rel ks ⊢
    ∃ (v : schema.List') (ksl : GoSlice), l ↦□ v ∗
      ⌜v.ElementRelationship' = rel.goName ∧ v.Keys' = ksl⌝ ∗ ksl ↦*{DFrac.discard} ks ∗
      isTypeRef v.ElementType' e

/-- A map type's fields (its `FindField` index stays inside `isMapRep`, for `Map.FindField`). -/
def isMapRep_elim.law : Prop :=
  ∀ m fs e rel, isMapRep (GF := GF) m fs e rel ⊢
    ∃ (fsl : GoSlice) (sfs : List schema.StructField) (etv : schema.TypeRef),
      m.[schema.Map, go!"Fields"] ↦□ fsl ∗ fsl ↦*{DFrac.discard} sfs ∗
      ⌜sfs.length = fs.length⌝ ∗
      □ (∀ (i : Nat) sf f, ⌜sfs[i]? = some sf ∧ fs[i]? = some f⌝ -∗ isStructField sf f) ∗
      m.[schema.Map, go!"Unions"] ↦□ slice.nil ∗
      m.[schema.Map, go!"ElementType"] ↦□ etv ∗ isTypeRefOpt etv e ∗
      m.[schema.Map, go!"ElementRelationship"] ↦□ rel.goName

/-- A map type's pointer is non-nil (Prove phase, 2026-11-19: `typed`'s `handleAtom`/`resolveSchema`
compare it with nil). -/
def isMapRep_nonnull.law : Prop :=
  ∀ m fs e rel, isMapRep (GF := GF) m fs e rel ⊢ ⌜m ≠ null⌝

/-- A list type's pointer is non-nil. -/
def isListRep_nonnull.law : Prop :=
  ∀ l e rel ks, isListRep (GF := GF) l e rel ks ⊢ ⌜l ≠ null⌝

/-- A field's name, default (none) and type. -/
def isStructField_elim.law : Prop :=
  ∀ sf f, isStructField (GF := GF) sf f ⊣⊢
    ⌜sf.Name' = f.1 ∧ sf.Default' = interface.nil⌝ ∗ isTypeRef sf.Type' f.2

end laws

/-! ## Pure laws: the premises of `FindNamedType`, `FindField`, `Resolve` from `Schema.WF` -/

/-- A schema in scope has distinct type names. -/
def Schema.WF_types_nodup.law : Prop :=
  ∀ S : Schema, S.WF → (S.types.map (·.1)).Nodup

/-- A schema in scope has distinct field names in each map type. -/
def Schema.WF_fields_nodup.law : Prop :=
  ∀ (S : Schema) n fs e rel, S.WF → S.find n = some (.map fs e rel) → (fs.map (·.1)).Nodup

end smd
end EtcdGrove
end Perennial
