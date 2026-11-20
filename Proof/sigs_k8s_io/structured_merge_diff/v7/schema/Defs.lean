/-
**structured-merge-diff's schemas, abstractly** (`schema` package, v7.0.0): the vocabulary of the
SMD API specs (`notes/smd-plan.md`, "The vocabulary").

A `Schema` is a list of named types. In the plan's scope every type reference is **named**
(`schema.TypeRef{NamedType: &n}`, no inlined atom, no element-relationship override), so an atom
never contains another atom and a schema is flat: a scalar, a list of a named element type, or a
map with named fields and an optional named element type. `Schema.WF` is the scope (decidable):
distinct type and field names, every reference resolves, lists atomic or associative with keys
(each a declared scalar field of the element map type), no unions, no defaults (the representation
predicate admits none).

`isSchema sc S` is **persistent**: SMD reads a schema from many goroutines (the API server shares
one per resource type). Its lazy indexes (`Schema.FindNamedType`'s and each `Map.FindField`'s:
a `sync.Once` and an `atomic.Pointer`) are `sync.isOnce` resources whose one-time action builds the
index. A schema literal (`freshSchema`, its indexes zero) becomes one by a ghost update
(`Laws.lean`, `isSchema_intro`).

Scope restrictions of the representation (`notes/smd-plan.md`, "Scope", (R)): a map type's
`Unions` is the nil slice (an empty non-nil `Unions` is excluded, though SMD treats it alike).
The representation's internals (`schemaRep`, `isAtom`, `lazyIndex`, ...) are sealed
(`@[no_expose]`): `newSchema`-style literals become `freshSchema` by `freshSchema_intro`.

The views of a shared schema's pieces that the `schema` package's own specs take and give
(`FindNamedType`, `Map.FindField`, `Resolve`, the `Equals` methods; their clients are `typed` and
`fieldpath`): `isAtomOpt` (an atom value, or the zero atom), `isListRep`, `isMapRep` (a `*List`,
a `*Map` with its `FindField` index), `isStructField` (a `StructField`), beside `isTypeRef`/
`isTypeRefOpt`. Sealed, with laws (`schema/Laws.lean`) to persist them and read their fields.

Lean-first (2026-11-19, notes/smd-plan.md); round 1's repairs 2026-11-19; the piece views added
with the `schema` package's per-function specs (Draft, 2026-11-19).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs
public import Perennial.Proof.sync.OnceDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

/-! ## Pure schemas -/

/-- `schema.Scalar`. -/
inductive Scalar where
  | numeric | string | boolean | untyped
  deriving DecidableEq, Inhabited

/-- `schema.ElementRelationship` (`unset`: the empty string, a map's default). -/
inductive ElemRel where
  | atomic | associative | separable | unset
  deriving DecidableEq, Inhabited

/-- A named `schema.TypeRef` (`NamedType`, `Nullable`; no inlined atom, no override). -/
structure TypeRef where
  name : GoString
  nullable : Bool := false
  deriving DecidableEq, Inhabited

/-- `schema.Atom` of a named type (exactly one of its three pointers non-nil). -/
inductive Atom where
  | scalar (s : Scalar)
  /-- A list: element type, relationship, key field names. -/
  | list (elem : TypeRef) (rel : ElemRel) (keys : List GoString)
  /-- A map (or struct): declared fields, element type of the other keys (`none`: the empty
  `TypeRef`, no other key allowed), relationship. -/
  | map (fields : List (GoString × TypeRef)) (elem : Option TypeRef) (rel : ElemRel)
  deriving Inhabited

/-- `schema.Schema`: its named types. -/
structure Schema where
  types : List (GoString × Atom)
  deriving Inhabited

/-- `Schema.FindNamedType` (names distinct under `Schema.WF`). -/
def Schema.find (S : Schema) (n : GoString) : Option Atom := lookupKV n S.types

/-- A reference resolves. -/
def Schema.resolves (S : Schema) (t : TypeRef) : Bool := (S.find t.name).isSome

/-- **`S.resolveRef ot`**: the atom `Schema.Resolve` returns for a reference without override:
the named type's (`ot = some t`), or the zero atom (`none`) for an unknown name or the empty
`TypeRef` (`ot = none`, whose `Inlined` atom is zero). -/
def Schema.resolveRef (S : Schema) : Option TypeRef → Option Atom
  | none => none
  | some t => S.find t.name

/-- Whether `Schema.Resolve` succeeds on a reference without override: the empty `TypeRef`
always (its zero `Inlined` atom), a named one when the name is defined. -/
def Schema.resolvesRef (S : Schema) : Option TypeRef → Bool
  | none => true
  | some t => S.resolves t

/-- The type of key `k` in a map type: its declared field's, else the element type
(`Map.FindField`, then `ElementType`). -/
def fieldType (fs : List (GoString × TypeRef)) (elem : Option TypeRef) (k : GoString) :
    Option TypeRef :=
  match lookupKV k fs with
  | some t => some t
  | none => elem

/-- A list's key field `k` is a declared scalar field of the element map type's fields `fs`. -/
def keyFieldOk (S : Schema) (fs : List (GoString × TypeRef)) (k : GoString) : Bool :=
  match lookupKV k fs with
  | some kt => match S.find kt.name with
    | some (.scalar _) => true
    | _ => false
  | none => false

/-- An atom in the plan's scope: a list atomic, or associative with distinct keys (at most `2^62`,
`FieldList.Sort`'s bound), each a declared scalar field of the element map type; a map's field names distinct; every reference resolves. -/
def Atom.wf (S : Schema) : Atom → Bool
  | .scalar _ => true
  | .list e rel ks => S.resolves e &&
      (decide (rel = .atomic) ||
       (decide (rel = .associative) && !ks.isEmpty && decide ks.Nodup &&
        decide (ks.length ≤ 2 ^ 62) &&
        match S.find e.name with
        | some (.map fs _ _) => ks.all (keyFieldOk S fs)
        | _ => false))
  | .map fs e _ => decide (fs.map (·.1)).Nodup && fs.all (fun f => S.resolves f.2) &&
      (match e with
       | some t => S.resolves t
       | none => true)

/-- **The scope's schemas** (`notes/smd-plan.md`, "Scope"): distinct type names, none the
reserved `__untyped_deduced_` (reconciliation skips it), every atom in scope (`Atom.wf`).
Computable: `decide` proves it of a literal. -/
def Schema.WF (S : Schema) : Prop :=
  (decide (S.types.map (·.1)).Nodup && !(S.types.map (·.1)).contains go!"__untyped_deduced_" &&
    S.types.all (fun na => na.2.wf S)) = true

instance (S : Schema) : Decidable S.WF := inferInstanceAs (Decidable (_ = true))

/-! ## Representation predicates -/

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The last element of a list with that name (a Go map built by assigning in order: the lazy
indexes). -/
@[no_expose] def lastNamed {α : Type} (name : α → GoString) (n : GoString) (xs : List α) : Option α :=
  xs.foldl (fun acc x => if name x = n then some x else acc) none

/-- `schema.Scalar`'s string. -/
def Scalar.goName : Scalar → GoString
  | .numeric => go!"numeric" | .string => go!"string" | .boolean => go!"boolean"
  | .untyped => go!"untyped"

/-- `schema.ElementRelationship`'s string. -/
def ElemRel.goName : ElemRel → GoString
  | .atomic => go!"atomic" | .associative => go!"associative" | .separable => go!"separable"
  | .unset => go!""

/-- An atom with no pointer set (`schema.Atom{}`). -/
@[no_expose] def atomZero (a : schema.Atom) : Prop := a.Scalar' = null ∧ a.List' = null ∧ a.Map' = null

/-- **`isTypeRef tr t`**: the `schema.TypeRef` `tr` names `t.name` (no inlined atom, no
override), nullable as `t` (persistent). -/
@[no_expose] def isTypeRef (tr : schema.TypeRef) (t : TypeRef) : IProp GF :=
  iprop(tr.NamedType' ↦□ t.name ∗
    ⌜atomZero tr.Inlined' ∧ tr.ElementRelationship' = null ∧ tr.Nullable' = t.nullable⌝)

/-- A map type's element type: `none` is the empty `schema.TypeRef{}`. -/
@[no_expose] def isTypeRefOpt (tr : schema.TypeRef) : Option TypeRef → IProp GF
  | none => iprop(⌜tr.NamedType' = null ∧ atomZero tr.Inlined' ∧ tr.ElementRelationship' = null ∧
      tr.Nullable' = false⌝)
  | some t => isTypeRef tr t

/-- A lazily built index (`Schema.FindNamedType`'s, `Map.FindField`'s): the `sync.Once` at `o` and
the `atomic.Pointer[map[string]T]` at `u`. `fresh`: both still zero (a literal's). Otherwise the
once's resource: its one-time action owns the pointer and leaves it pointing (for good, read-only)
to an index `M` with `ok M`. -/
@[no_expose] def lazyIndex {T : Type} [ZeroVal T] (fresh : Bool) (o u : Loc) (ok : GMap GoString T → Prop) :
    IProp GF :=
  if fresh then iprop(o ↦ (zero_val sync.Once) ∗ u ↦ (zero_val (sync.atomic.Pointer GoMap)))
  else sync.isOnce o iprop(u ↦ (zero_val (sync.atomic.Pointer GoMap)))
      iprop(∃ (mp mm : Loc) (M : GMap GoString T),
        sync.atomic.ownPointer (T' := GoMap) u DFrac.discard mp ∗
        mp ↦□ mm ∗ mm ↦$□ M ∗ ⌜ok M⌝)

/-- **`isStructField sf f`**: the `schema.StructField` `sf` is the declared field `f` (its name and
named type), without a default (scope: `Default` the nil interface; persistent). -/
@[no_expose] def isStructField (sf : schema.StructField) (f : GoString × TypeRef) : IProp GF :=
  iprop(⌜sf.Name' = f.1 ∧ sf.Default' = interface.nil⌝ ∗ isTypeRef sf.Type' f.2)

/-- A map type's `schema.StructField`s (no default). -/
@[no_expose] def isFields : List schema.StructField → List (GoString × TypeRef) → IProp GF
  | [], [] => iprop(True)
  | f :: fs, nt :: rest => iprop(isStructField f nt ∗ isFields fs rest)
  | _, _ => iprop(False)

/-- **`isListRep l e rel ks`**: the `*schema.List` at `l` (read-only) has element type `e`,
relationship `rel` and key field names `ks` (persistent). -/
@[no_expose] def isListRep (l : Loc) (e : TypeRef) (rel : ElemRel) (ks : List GoString) : IProp GF :=
  iprop(∃ (v : schema.List') (ksl : GoSlice), l ↦□ v ∗ ⌜v.ElementRelationship' = rel.goName ∧
    v.Keys' = ksl⌝ ∗ ksl ↦*{DFrac.discard} ks ∗ isTypeRef v.ElementType' e)

/-- The `*schema.Map` at `m` (read-only fields) with declared fields `fs`, element type `e`,
relationship `rel`, no unions, and its `FindField` index (`fresh`: still zero); `m` non-nil (a
field's points-to does not give it: `structFieldRef` of nil is unconstrained; Prove phase,
2026-11-19, for `isMapRep_nonnull`). -/
@[no_expose] def mapRep (fresh : Bool) (m : Loc) (fs : List (GoString × TypeRef))
    (e : Option TypeRef) (rel : ElemRel) : IProp GF :=
  iprop(⌜m ≠ null⌝ ∗ ∃ (fsl : GoSlice) (sfs : List schema.StructField) (us : GoSlice) (etv : schema.TypeRef),
      m.[schema.Map, go!"Fields"] ↦□ fsl ∗ fsl ↦*{DFrac.discard} sfs ∗ isFields sfs fs ∗
      m.[schema.Map, go!"Unions"] ↦□ us ∗ ⌜us = slice.nil⌝ ∗
      m.[schema.Map, go!"ElementType"] ↦□ etv ∗ isTypeRefOpt etv e ∗
      m.[schema.Map, go!"ElementRelationship"] ↦□ rel.goName ∗
      lazyIndex (T := schema.StructField) fresh m.[schema.Map, go!"once"]
        m.[schema.Map, go!"m"] (fun M => ∀ n, M !! n = lastNamed (·.Name') n sfs))

/-- **`isMapRep m fs e rel`**: the `*schema.Map` at `m`, a map type of a shared schema
(`isSchema`): declared fields `fs`, element type `e`, relationship `rel`, no unions, its
`FindField` index under its once (persistent). -/
@[no_expose] def isMapRep (m : Loc) (fs : List (GoString × TypeRef)) (e : Option TypeRef)
    (rel : ElemRel) : IProp GF := mapRep false m fs e rel

/-- The `schema.Atom` `a` of a named type holding `A`, with its map's `FindField` index. -/
@[no_expose] def isAtom (fresh : Bool) (a : schema.Atom) : Atom → IProp GF
  | .scalar s => iprop(a.Scalar' ↦□ s.goName ∗ ⌜a.List' = null ∧ a.Map' = null⌝)
  | .list e rel ks => iprop(⌜a.Scalar' = null ∧ a.Map' = null⌝ ∗ isListRep a.List' e rel ks)
  | .map fs e rel => iprop(⌜a.Scalar' = null ∧ a.List' = null⌝ ∗ mapRep fresh a.Map' fs e rel)

/-- **`isAtomOpt a oA`**: the `schema.Atom` value `a` (a copy of a shared schema's atom: its
pointers shared) holds `A` when `oA = some A`, and is the zero atom `schema.Atom{}` when
`oA = none` (an empty `TypeRef`'s `Inlined`, `Resolve`'s result for the empty `TypeRef` or an
unknown name). Persistent. What `Schema.Resolve` returns and `Atom.Equals` compares. -/
@[no_expose] def isAtomOpt (a : schema.Atom) : Option Atom → IProp GF
  | none => iprop(⌜atomZero a⌝)
  | some A => isAtom false a A

/-- **`freshAtom a A`**: a schema literal's atom holding `A`, its `FindField` index still zero
(the piece of a `freshSchema` its intro law takes: `freshAtom_*`, `freshSchema_intro`). -/
@[no_expose] def freshAtom (a : schema.Atom) (A : Atom) : IProp GF := isAtom true a A

/-- A schema's `schema.TypeDef`s. -/
@[no_expose] def isTypeDefs (fresh : Bool) : List schema.TypeDef → List (GoString × Atom) → IProp GF
  | [], [] => iprop(True)
  | td :: tds, (n, a) :: rest => iprop(⌜td.Name' = n⌝ ∗ isAtom fresh td.Atom' a ∗
      isTypeDefs fresh tds rest)
  | _, _ => iprop(False)

/-- A `*schema.Schema` holding `S`, its lazy indexes `fresh` or under their onces. Its `lock` and
`resolvedTypes` are not owned: `Resolve` takes them only for a reference with an
element-relationship override, which the scope has none of. -/
@[no_expose] def schemaRep (fresh : Bool) (sc : Loc) (S : Schema) : IProp GF :=
  iprop(∃ (tys : GoSlice) (tds : List schema.TypeDef),
    sc.[schema.Schema, go!"Types"] ↦□ tys ∗ tys ↦*{DFrac.discard} tds ∗ isTypeDefs fresh tds S.types ∗
    lazyIndex (T := schema.TypeDef) fresh sc.[schema.Schema, go!"once"] sc.[schema.Schema, go!"m"]
      (fun M => ∀ n, M !! n = lastNamed (·.Name') n tds))

/-- **`isSchema sc S`**: the `*schema.Schema` at `sc` holds `S` (persistent; see the header). -/
@[no_expose] def isSchema (sc : Loc) (S : Schema) : IProp GF := schemaRep false sc S

/-- **`freshSchema sc S`**: a schema literal (`&schema.Schema{Types: ...}`), its lazy indexes still
zero, owned; `isSchema_intro` makes it an `isSchema`. -/
@[no_expose] def freshSchema (sc : Loc) (S : Schema) : IProp GF := schemaRep true sc S

end own

end smd
end EtcdGrove
end Perennial
