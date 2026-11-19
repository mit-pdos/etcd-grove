/-
**Representation predicates** of structured-merge-diff's (SMD's) Go values, relating them to the
pure model (`Model/*.lean`): what the specs of SMD's API (`Spec/sigs_k8s_io/structured_merge_diff/
v7/`) are stated over. Lean-first (2026-11-19, notes/smd-robustness.md).

Ownership is **persistent** (discarded fractions, `↦□`) for every value an SMD call reads and
returns, which SMD never writes after building it: unstructured values (`ownU`, `ownValue`), path
elements, paths, field sets (`ownSet`), versioned sets, managed fields (`ownMF`), typed values
(`ownTV`), conflicts. A caller that built such a value with full ownership gives it up for
reading (as the driver does with its literals). The exception is the **schema** (`ownSchema`):
`Schema.FindNamedType` and `Map.FindField` build their indexes lazily (`sync.Once`,
`atomic.Pointer`), so the schema's caches are owned exclusively and threaded through the calls
(`ownLazyIndex`: still zero, as a fresh literal leaves them, or built). Its immutable parts
(types, fields, element types) are persistent.

What the predicates exclude (the model's restrictions, `Model/Merge.lean`'s header): values other
than unstructured `nil`/`bool`/`int64`/`string`/`[]interface{}`/`map[string]interface{}` (a
non-nil map, its model's keys sorted); a `TypeRef` with an `ElementRelationship` override; a map
type with unions; a field with a default; a `VersionedSet` that is not a `versionedSet`.
-/
module

public import GeneratedProof.sigs_k8s_io.structured_merge_diff.v7.merge
public import Perennial.Proof.sync.OnceDefs
public import Perennial.Proof.sync.atomic.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.Model.Merge

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

/-! ## Pure helpers -/

/-- The keys are strictly increasing (`gsCompare`): a model map's canonical form. -/
def keysSorted {α : Type} : List (GoString × α) → Bool
  | [] => true
  | [_] => true
  | (k, _) :: (k', v') :: rest => gsLt k k' && keysSorted ((k', v') :: rest)

/-- The last element of a list with that name (a Go map built by assigning in order). -/
def lastNamed {α : Type} (name : α → GoString) (n : GoString) (xs : List α) : Option α :=
  xs.foldl (fun acc x => if name x = n then some x else acc) none

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : merge.Assumptions]

/-- `interface{}`. -/
abbrev ifaceTy : go.GoType := go.GoType.InterfaceType []
/-- `map[string]interface{}`. -/
abbrev mapStrIfaceTy : go.GoType := go.GoType.MapType go.string ifaceTy
/-- `[]interface{}`. -/
abbrev sliceIfaceTy : go.GoType := go.GoType.SliceType ifaceTy

/-! ## Unstructured values -/

mutual
/-- An `interface{}` holding the unstructured value `x`. -/
def ownU (i : GoInterface) : UVal → IProp GF
  | .null => iprop(⌜i = interface.nil⌝)
  | .bool b => iprop(⌜i = interface.mkOk go.bool #b⌝)
  | .int n => iprop(⌜i = interface.mkOk go.int64 #n⌝)
  | .str s => iprop(⌜i = interface.mkOk go.string #s⌝)
  | .list vs => iprop(∃ (sl : GoSlice) (xs : List GoInterface),
      ⌜i = interface.mkOk sliceIfaceTy #sl⌝ ∗ sl ↦*{DFrac.discard} xs ∗ ownUL xs vs)
  | .map kvs => iprop(∃ (m : GoMap) (M : GMap GoString GoInterface),
      ⌜i = interface.mkOk mapStrIfaceTy #m⌝ ∗ m ↦$□ M ∗
      ⌜keysSorted kvs = true ∧ ∀ k, (M !! k).isSome = (lookupKV k kvs).isSome⌝ ∗ ownUM M kvs)
  termination_by structural x => x
/-- A list's items. -/
def ownUL : List GoInterface → List UVal → IProp GF
  | [], [] => iprop(True)
  | x :: xs, v :: vs => iprop(ownU x v ∗ ownUL xs vs)
  | _, _ => iprop(False)
  termination_by structural _ vs => vs
/-- A map's entries. -/
def ownUM (M : GMap GoString GoInterface) : List (GoString × UVal) → IProp GF
  | [] => iprop(True)
  | (k, v) :: kvs => iprop(∃ x, ⌜M !! k = some x⌝ ∗ ownU x v ∗ ownUM M kvs)
  termination_by structural kvs => kvs
end

/-- A `map[string]interface{}` (the map itself, not in an interface) holding `kvs`. -/
def ownUMap (m : GoMap) (kvs : List (GoString × UVal)) : IProp GF :=
  iprop(∃ M : GMap GoString GoInterface, m ↦$□ M ∗
    ⌜keysSorted kvs = true ∧ ∀ k, (M !! k).isSome = (lookupKV k kvs).isSome⌝ ∗ ownUM M kvs)

/-- A `value.Value` built by `NewValueInterface` (a `*valueUnstructured`) holding `x`. -/
def ownValue (v : value.Value) (x : UVal) : IProp GF :=
  iprop(∃ (p : Loc) (i : GoInterface),
    ⌜v = interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #p⌝ ∗
    p ↦□ (value.valueUnstructured.mk i) ∗ ownU i x)

/-- A `value.Value` that may be `nil` (`none`). -/
def ownValueOpt (v : value.Value) : Option UVal → IProp GF
  | none => iprop(⌜v = interface.nil⌝)
  | some x => ownValue v x

/-! ## Paths -/

/-- A `value.FieldList`'s fields. -/
def ownFieldsL : List value.Field → FieldList → IProp GF
  | [], [] => iprop(True)
  | f :: fs, (n, x) :: rest => iprop(⌜f.Name' = n⌝ ∗ ownValue f.Value' x ∗ ownFieldsL fs rest)
  | _, _ => iprop(False)

/-- A `value.FieldList` slice. -/
def ownFieldList (s : GoSlice) (fl : FieldList) : IProp GF :=
  iprop(∃ fs : List value.Field, s ↦*{DFrac.discard} fs ∗ ownFieldsL fs fl)

/-- A `fieldpath.PathElement`: its first non-nil field is the model's. -/
def ownPE (e : fieldpath.PathElement) : PE → IProp GF
  | .field n => iprop(e.FieldName' ↦□ n)
  | .key fl => iprop(⌜e.FieldName' = null⌝ ∗ ∃ s : GoSlice, e.Key' ↦□ s ∗ ownFieldList s fl)
  | .value x => iprop(⌜e.FieldName' = null ∧ e.Key' = null⌝ ∗
      ∃ v : value.Value, e.Value' ↦□ v ∗ ownValue v x)
  | .index i => iprop(⌜e.FieldName' = null ∧ e.Key' = null ∧ e.Value' = null⌝ ∗ e.Index' ↦□ i)
  | .invalid => iprop(⌜e.FieldName' = null ∧ e.Key' = null ∧ e.Value' = null ∧ e.Index' = null⌝)

/-- A list of path elements. -/
def ownPEL : List fieldpath.PathElement → List PE → IProp GF
  | [], [] => iprop(True)
  | e :: es, pe :: pes => iprop(ownPE e pe ∗ ownPEL es pes)
  | _, _ => iprop(False)

/-- A `fieldpath.Path` (a slice of path elements). -/
def ownPath (s : GoSlice) (p : Path) : IProp GF :=
  iprop(∃ es : List fieldpath.PathElement, s ↦*{DFrac.discard} es ∗ ownPEL es p)

/-- A list of paths (the elements of a `[]fieldpath.Path`). -/
def ownPaths : List GoSlice → List Path → IProp GF
  | [], [] => iprop(True)
  | s :: ss, p :: ps => iprop(ownPath s p ∗ ownPaths ss ps)
  | _, _ => iprop(False)

/-! ## Sets -/

mutual
/-- A `*fieldpath.Set`: its members' and children's slices, the trie of the model. -/
def ownSet (p : Loc) : PSet → IProp GF
  | .mk ms cs => iprop(∃ (v : fieldpath.Set') (es : List fieldpath.PathElement)
      (ns : List fieldpath.setNode),
      p ↦□ v ∗ v.Members'.members' ↦*{DFrac.discard} es ∗ ownPEL es ms ∗
      v.Children'.members' ↦*{DFrac.discard} ns ∗ ownNodes ns cs)
  termination_by structural s => s
/-- A `SetNodeMap`'s nodes. -/
def ownNodes : List fieldpath.setNode → List (PE × PSet) → IProp GF
  | [], [] => iprop(True)
  | n :: ns, (pe, s) :: cs => iprop(ownPE n.pathElement' pe ∗ ownSet n.set' s ∗ ownNodes ns cs)
  | _, _ => iprop(False)
  termination_by structural _ cs => cs
end

/-- A `fieldpath.VersionedSet` (a `versionedSet`). -/
def ownVSet (i : fieldpath.VersionedSet) (vs : VSet) : IProp GF :=
  iprop(∃ p : Loc,
    ⌜i = interface.mkOk fieldpath.versionedSet.ty #(fieldpath.versionedSet.mk p vs.version vs.applied)⌝ ∗
    ownSet p vs.set)

/-- The managers' entries of a `ManagedFields` map. -/
def ownMFL (M : GMap GoString GoInterface) : MF → IProp GF
  | [] => iprop(True)
  | (k, vs) :: rest => iprop(∃ i, ⌜M !! k = some i⌝ ∗ ownVSet i vs ∗ ownMFL M rest)

/-- A `fieldpath.ManagedFields` (a non-nil Go map). -/
def ownMF (m : fieldpath.ManagedFields) (mf : MF) : IProp GF :=
  iprop(∃ M : GMap GoString GoInterface, m ↦$□ M ∗
    ⌜keysSorted mf = true ∧ ∀ k, (M !! k).isSome = (lookupKV k mf).isSome⌝ ∗ ownMFL M mf)

/-! ## Schemas -/

/-- A lazily built index of a schema or a map type (`Schema.FindNamedType`'s,
`Map.FindField`'s): the `sync.Once` at `o` and the `atomic.Pointer[map[string]T]` at `u`, either
both still zero (a fresh literal's), or the once's state with the index built: `u` then points
(for good) to a map `M` with `ok M`. -/
def ownLazyIndex {T : Type} [ZeroVal T] (o u : Loc) (ok : GMap GoString T → Prop) : IProp GF :=
  iprop((o ↦ (zero_val sync.Once) ∗ u ↦ (zero_val (sync.atomic.Pointer GoMap))) ∨
    sync.isOnce o iprop(u ↦ (zero_val (sync.atomic.Pointer GoMap)))
      iprop(∃ (mp mm : Loc) (M : GMap GoString T),
        sync.atomic.ownPointer (T' := GoMap) u DFrac.discard mp ∗
        mp ↦□ mm ∗ mm ↦$□ M ∗ ⌜ok M⌝))

/-- A pointer that is `nil` for `none`, else to the string. -/
def ownStrPtr (p : Loc) : Option GoString → IProp GF
  | none => iprop(⌜p = null⌝)
  | some s => iprop(p ↦□ s)

mutual
/-- A `schema.TypeRef` (no `ElementRelationship` override). `c`: with the lazy indexes of the
map types it reaches (`ownSchema`'s types), or without (a typed value's type, named). -/
def ownTypeRef (c : Bool) (t : schema.TypeRef) : TypeRef → IProp GF
  | .mk n a nl => iprop(⌜t.ElementRelationship' = null ∧ t.Nullable' = nl⌝ ∗
      ownStrPtr t.NamedType' n ∗ ownAtom c t.Inlined' a)
  termination_by structural x => x
/-- A `schema.Atom`. -/
def ownAtom (c : Bool) (a : schema.Atom) : Atom → IProp GF
  | .mk s l m => iprop(ownStrPtr a.Scalar' s ∗ ownOptList c a.List' l ∗ ownOptMap c a.Map' m)
  termination_by structural x => x
/-- An atom's `*schema.List`. -/
def ownOptList (c : Bool) (p : Loc) : OptListT → IProp GF
  | .none => iprop(⌜p = null⌝)
  | .some l => ownListT c p l
  termination_by structural x => x
/-- An atom's `*schema.Map`. -/
def ownOptMap (c : Bool) (p : Loc) : OptMapT → IProp GF
  | .none => iprop(⌜p = null⌝)
  | .some m => ownMapT c p m
  termination_by structural x => x
/-- A `*schema.List`. -/
def ownListT (c : Bool) (p : Loc) : ListT → IProp GF
  | .mk et er ks => iprop(∃ v : schema.List', p ↦□ v ∗ ⌜v.ElementRelationship' = er⌝ ∗
      v.Keys' ↦*{DFrac.discard} ks ∗ ownTypeRef c v.ElementType' et)
  termination_by structural x => x
/-- A `*schema.Map`: its fields (no defaults; a `nil` slice if none), no unions, its element
type and relationship; with `c`, its `FindField` index. -/
def ownMapT (c : Bool) (p : Loc) : MapT → IProp GF
  | .mk fs et er => iprop(∃ (fsl : GoSlice) (sfs : List schema.StructField) (us : GoSlice)
      (etv : schema.TypeRef),
      p.[schema.Map, go!"Fields"] ↦□ fsl ∗ fsl ↦*{DFrac.discard} sfs ∗
      ⌜sfs = [] → fsl = slice.nil⌝ ∗
      p.[schema.Map, go!"Unions"] ↦□ us ∗ ⌜us = slice.nil⌝ ∗
      p.[schema.Map, go!"ElementType"] ↦□ etv ∗ p.[schema.Map, go!"ElementRelationship"] ↦□ er ∗
      ownTypeRef c etv et ∗ ownSFields c sfs fs ∗
      (if c then ownLazyIndex (T := schema.StructField) p.[schema.Map, go!"once"]
        p.[schema.Map, go!"m"] (fun M => ∀ n, M !! n = lastNamed (·.Name') n sfs)
       else iprop(True)))
  termination_by structural x => x
/-- A map type's `schema.StructField`s. -/
def ownSFields (c : Bool) : List schema.StructField → Fields → IProp GF
  | [], .nil => iprop(True)
  | f :: fs, .cons (.mk n t) rest => iprop(⌜f.Name' = n ∧ f.Default' = interface.nil⌝ ∗
      ownTypeRef c f.Type' t ∗ ownSFields c fs rest)
  | _, _ => iprop(False)
  termination_by structural _ x => x
end

/-- A schema's `schema.TypeDef`s, with their map types' indexes. -/
def ownTypeDefs : List schema.TypeDef → List (GoString × Atom) → IProp GF
  | [], [] => iprop(True)
  | td :: tds, (n, a) :: rest => iprop(⌜td.Name' = n⌝ ∗ ownAtom true td.Atom' a ∗ ownTypeDefs tds rest)
  | _, _ => iprop(False)

/-- A `*schema.Schema` holding `S` (exclusive: its lazy indexes). Its `lock` and
`resolvedTypes` are untouched (no `ElementRelationship` override: `Resolve` never takes them). -/
def ownSchema (sc : Loc) (S : Schema) : IProp GF :=
  iprop(∃ (tys : GoSlice) (tds : List schema.TypeDef),
    sc.[schema.Schema, go!"Types"] ↦□ tys ∗ tys ↦*{DFrac.discard} tds ∗ ownTypeDefs tds S.types ∗
    ownLazyIndex (T := schema.TypeDef) sc.[schema.Schema, go!"once"] sc.[schema.Schema, go!"m"]
      (fun M => ∀ n, M !! n = lastNamed (·.Name') n tds) ∗
    sc.[schema.Schema, go!"lock"] ↦ (zero_val sync.Mutex) ∗
    sc.[schema.Schema, go!"resolvedTypes"] ↦ (zero_val GoMap))

/-! ## Typed values, the updater, conflicts -/

/-- A `*typed.TypedValue` of the schema at `sc` holding `tv`. -/
def ownTV (p : Loc) (sc : Loc) (tv : TV) : IProp GF :=
  iprop(∃ (v : value.Value) (tr : schema.TypeRef),
    p ↦□ (typed.TypedValue.mk v tr sc) ∗ ownValueOpt v tv.value ∗ ownTypeRef false tr tv.typeRef)

/-- A `*typed.TypedValue` that may be `nil` (`none`). -/
def ownTVOpt (p : Loc) (sc : Loc) : Option TV → IProp GF
  | none => iprop(⌜p = null⌝)
  | some tv => ownTV p sc tv

/-- A `merge.Converter` that is the identity on one API version: `Convert(obj, v)` returns
`(obj, nil)`, `IsMissingVersionError(err)` returns `false` (as Hoare triples on the methods of
its dynamic type). -/
def isIdentityConverter (cv : merge.Converter) : IProp GF :=
  iprop(∃ (T : go.GoType) (v : val), ⌜cv = interface.mkOk T v⌝ ∗
    □ (∀ (p : Loc) (ver : fieldpath.APIVersion) (Φ : val → IProp GF),
        ▷ Φ (PairV #p #(interface.nil : GoInterface)) -∗
        WP (App (App (Val #(methods T go!"Convert" v)) (Val #p)) (Val #ver)) {{ Φ }}) ∗
    □ (∀ (e : GoInterface) (Φ : val → IProp GF), ▷ Φ #false -∗
        WP (App (Val #(methods T go!"IsMissingVersionError" v)) (Val #e)) {{ Φ }}))

/-- A `*merge.Updater` with an identity converter, no ignored fields or filter. -/
def ownUpdater (u : Loc) (returnInputOnNoop : Bool) : IProp GF :=
  iprop(∃ cv : merge.Converter, u ↦□ (merge.Updater.mk cv (zero_val GoMap) (zero_val GoMap) returnInputOnNoop) ∗
    isIdentityConverter cv)

/-- A `merge.Conflicts` slice's conflicts. -/
def ownConflictL : List merge.Conflict → List Conflict → IProp GF
  | [], [] => iprop(True)
  | x :: xs, c :: cs => iprop(⌜x.Manager' = c.manager⌝ ∗ ownPath x.Path' c.path ∗ ownConflictL xs cs)
  | _, _ => iprop(False)

/-- A `merge.Conflicts`. -/
def ownConflicts (s : merge.Conflicts) (cs : List Conflict) : IProp GF :=
  iprop(∃ xs : List merge.Conflict, s ↦*{DFrac.discard} xs ∗ ownConflictL xs cs)

/-! ## The outcomes of `Updater.Apply` and `Updater.Update` -/

/-- What `Updater.Apply` returns (`op`, `mfm`, `err`) for the model's outcome `r`: the new object
(`nil` for a no-op without `ReturnInputOnNoop`) and managers; or a `Conflicts` error holding the
model's conflicts with the managers in some order (Go ranges over a map), with no object and an
empty `ManagedFields`; or another error, with no object and an empty `ManagedFields`. -/
def applyPost (r : ApplyRes) (sc op : Loc) (mfm : GoMap) (err : GoInterface) : IProp GF :=
  match r with
  | .ok obj mf => iprop(⌜err = interface.nil⌝ ∗ ownTVOpt op sc obj ∗ ownMF mfm mf)
  | .conflicts cs => iprop(⌜op = null⌝ ∗ ownMF mfm [] ∗ ∃ (s : merge.Conflicts) (order : MF),
      ⌜err = interface.mkOk merge.Conflicts.ty #s ∧ order.Perm cs⌝ ∗ ownConflicts s (conflictsOf order))
  | .error => iprop(⌜op = null ∧ err ≠ interface.nil⌝ ∗ ownMF mfm [])
  | .panic => iprop(False)

/-- What `Updater.Update` returns for the model's outcome `r`: its argument `np` (the new
object) and the managers; or an error, with no object and an empty `ManagedFields`. -/
def updatePost (r : UpdateRes) (np op : Loc) (mfm : GoMap) (err : GoInterface) : IProp GF :=
  match r with
  | .ok mf => iprop(⌜op = np ∧ err = interface.nil⌝ ∗ ownMF mfm mf)
  | .error => iprop(⌜op = null ∧ err ≠ interface.nil⌝ ∗ ownMF mfm [])
  | .panic => iprop(False)

end own

end smd
end EtcdGrove
end Perennial
