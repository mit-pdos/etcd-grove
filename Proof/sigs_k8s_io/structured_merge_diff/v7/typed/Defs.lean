/-
**structured-merge-diff's typed operations, abstractly** (`typed` package, v7.0.0): the vocabulary
of the SMD API specs (`notes/smd-plan.md`, "The vocabulary").

What a value of a type is, and what SMD's typed operations compute, as functions of pure values
(`UVal`), a pure schema (`Schema`) and a named type (`TypeRef`), on the values the scope admits
(`conforms`: the values `typed.AsTyped` accepts; on others the functions are arbitrary):

- `conforms S t x`: `x` validates against `t` (`TypedValue.Validate`);
- `keyOf ks x`: an associative list item's key (`keyedAssociativeListItemToPathElement`);
- `fieldSet S t x`: the fields `x` sets (`TypedValue.ToFieldSet`): every scalar, atomic list or
  map, list item, and map entry that is `null`, `{}` or not a declared field;
- `removeItems S t x R`: `x` without the paths `R` (`TypedValue.RemoveItems`), a container that
  becomes (or is) empty on the way turned into `null` (SSA-01/02's mechanism);
- `merge S t l r`: `r` merged into `l` (`TypedValue.Merge`): the right side's scalars and atomic
  values win, maps merge per key, associative lists per item key in `mergeKeys`'s order;
- `compare S t l r`: what changed from `l` to `r` (`TypedValue.Compare`): removed, modified and
  added paths;
- `ensureNamed S t s`: `s` with every declared struct field that has a path below it
  (`Set.EnsureNamedFieldsAreMembers`);
- `reconcile S t s`: `s` with every subtree below an atomic type collapsed to the atomic node
  (`ReconcileFieldSetWithSchema`; the identity on a set written at this schema).

Each is defined by recursion over the value (or the path), not over SMD's walkers; `merge` and
`compare` recurse over two values at once, with fuel (`size l + size r + 1` is enough). The only
definition that follows SMD's loop step by step is `mergeOrderF`: the order of an associative
list's items after a merge has no simpler description (it is observable: the driver's step 7).

Lean-first (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

attribute [local instance] Classical.propDecidable

open PathSet

/-! ## Keys -/

/-- Insert into a field list sorted by name (stable). -/
def flInsert (f : GoString × UVal) : FieldList → FieldList
  | [] => [f]
  | g :: gs => if gsLt f.1 g.1 then f :: g :: gs else g :: flInsert f gs

/-- `FieldList.Sort`: by name (the key names are distinct under `Schema.WF`, so stability does
not matter). -/
def flSort (fl : FieldList) : FieldList := fl.foldl (fun acc f => flInsert f acc) []

/-- **The key of an associative list item** with key fields `ks`: the key fields it has, sorted
by name; `none` for an item that is not a map or has none of them. -/
def keyOf (ks : List GoString) : UVal → Option PE
  | .map kvs =>
    let fl := ks.filterMap (fun k => (lookupKV k kvs).map (fun v => (k, v)))
    if fl = [] then none else some (.key (flSort fl))
  | _ => none

/-- The item of `vs` with key `pe`. -/
def itemOf (ks : List GoString) (vs : List UVal) (pe : PE) : Option UVal :=
  vs.find? (fun v => decide (keyOf ks v = some pe))

/-- The keys of a list's items. -/
def keysOf (ks : List GoString) (vs : List UVal) : List PE := vs.filterMap (keyOf ks)

/-! ## Conformance -/

/-- A scalar of a scalar type (`validateScalar`; no floats in scope). -/
def scalarOk : Scalar → UVal → Prop
  | _, .null => True
  | .numeric, .int _ => True
  | .string, .str _ => True
  | .boolean, .bool _ => True
  | .untyped, .int _ => True
  | .untyped, .str _ => True
  | .untyped, .bool _ => True
  | _, _ => False

mutual
/-- **`conforms S t x`**: `x` validates against the type `t` of `S` (`TypedValue.Validate`,
without `AllowDuplicates`): a scalar of its kind or `null`; `null` or a list whose items conform to
the element type, for an associative list each with a key and no key twice; `null` or a map whose
every key is a declared field or, if the type has one, of the element type, its value
conforming. -/
def conforms (S : Schema) (t : TypeRef) : UVal → Prop
  | .list vs => match S.find t.name with
    | some (.list e rel ks) => conformsL S e vs ∧
        (rel = .associative → (∀ v ∈ vs, (keyOf ks v).isSome) ∧ (keysOf ks vs).Nodup)
    | _ => False
  | .map kvs => match S.find t.name with
    | some (.map fs e _) => conformsM S fs e kvs
    | _ => False
  | x => match S.find t.name with
    | some (.scalar s) => scalarOk s x
    | some _ => x = .null
    | none => False
/-- A list's items. -/
def conformsL (S : Schema) (e : TypeRef) : List UVal → Prop
  | [] => True
  | v :: vs => conforms S e v ∧ conformsL S e vs
/-- A map's entries. -/
def conformsM (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef) :
    List (GoString × UVal) → Prop
  | [] => True
  | (k, v) :: kvs => (match fieldType fs e k with
      | some t => conforms S t v
      | none => False) ∧ conformsM S fs e kvs
end

/-! ## Field sets -/

/-- `{p}`, nothing for the root. -/
abbrev ins (p : Path) : PathSet := PathSet.single p

mutual
/-- The fields `x` sets at path `p`, `x` of type `t`. -/
def fieldsAt (S : Schema) (t : TypeRef) (p : Path) : UVal → PathSet
  | .list vs => match S.find t.name with
    | some (.list _ .atomic _) => ins p
    | some (.list e _ ks) => fieldsL S e ks p vs
    | _ => empty
  | .map kvs => match S.find t.name with
    | some (.map _ _ .atomic) => ins p
    | some (.map fs e _) => fieldsM S fs e p kvs
    | _ => empty
  | _ => match S.find t.name with
    | some (.scalar _) => ins p
    | some (.list _ .atomic _) => ins p
    | some (.map _ _ .atomic) => ins p
    | _ => empty
/-- An associative list's items: each item, and what it sets (no key twice: conformance). -/
def fieldsL (S : Schema) (e : TypeRef) (ks : List GoString) (p : Path) : List UVal → PathSet
  | [] => empty
  | v :: vs => match keyOf ks v with
    | some pe => union (union (fieldsAt S e (p ++ [pe]) v) (ins (p ++ [pe]))) (fieldsL S e ks p vs)
    | none => fieldsL S e ks p vs
/-- A granular map's entries: what each sets, and the entry itself if it is `null`, `{}` or not a
declared field. -/
def fieldsM (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (p : Path) :
    List (GoString × UVal) → PathSet
  | [] => empty
  | (k, v) :: kvs =>
    union (match fieldType fs e k with
      | some t => union (fieldsAt S t (p ++ [.field k]) v)
          (if v = .null ∨ v = .map [] ∨ lookupKV k fs = none then ins (p ++ [.field k]) else empty)
      | none => empty)
    (fieldsM S fs e p kvs)
end

/-- **`fieldSet S t x`**: the fields `x` sets (`TypedValue.ToFieldSet`). -/
def fieldSet (S : Schema) (t : TypeRef) (x : UVal) : PathSet := fieldsAt S t [] x

/-! ## Removing paths -/

mutual
/-- `x` of type `t` without the paths `R` (relative to `x`). -/
def removeAt (S : Schema) (t : TypeRef) (R : PathSet) : UVal → UVal
  | .list vs => match S.find t.name with
    | some (.list e rel ks) =>
      if vs.isEmpty ∨ rel = .atomic then .null else
      match removeL S e ks R vs with
      | [] => .null
      | out => .list out
    | some (.scalar _) => .list vs
    | _ => .null
  | .map kvs => match S.find t.name with
    | some (.map fs e rel) =>
      if kvs.isEmpty ∨ rel = .atomic then .null else
      match removeM S fs e R kvs with
      | [] => .null
      | out => .map out
    | some (.scalar _) => .map kvs
    | _ => .null
  | x => match S.find t.name with
    | some (.scalar _) => x
    | _ => .null
/-- A list's items: an item whose path is in `R` goes, one with paths of `R` below it loses
them. -/
def removeL (S : Schema) (e : TypeRef) (ks : List GoString) (R : PathSet) : List UVal → List UVal
  | [] => []
  | v :: vs => match keyOf ks v with
    | some pe =>
      if R [pe] then removeL S e ks R vs
      else if ¬ (R.under pe).IsEmpty then removeAt S e (R.under pe) v :: removeL S e ks R vs
      else v :: removeL S e ks R vs
    | none => v :: removeL S e ks R vs
/-- A map's entries, likewise. -/
def removeM (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (R : PathSet) :
    List (GoString × UVal) → List (GoString × UVal)
  | [] => []
  | (k, v) :: kvs =>
    if R [.field k] then removeM S fs e R kvs
    else if ¬ (R.under (.field k)).IsEmpty then
      (k, match fieldType fs e k with
        | some t => removeAt S t (R.under (.field k)) v
        | none => .null) :: removeM S fs e R kvs
    else (k, v) :: removeM S fs e R kvs
end

/-- **`removeItems S t x R`**: `x` without the paths `R` (`TypedValue.RemoveItems`); see the file
header. -/
def removeItems (S : Schema) (t : TypeRef) (x : UVal) (R : PathSet) : UVal := removeAt S t R x

/-! ## Merging -/

/-- The order of an associative list's items after a merge (`mergingWalker.visitListItems`'s
loop, step by step): `L` the live keys left, `R` the configuration's, `sh` the shared keys not
merged yet in `R`'s order (its head `nextShared`), `mg` the keys merged. A shared key the left side
reaches out of `R`'s order is skipped there and placed where `R` has it; a left-only key stays
where the left side has it. -/
def mergeOrderF : Nat → (PE → Prop) → List PE → List PE → List PE → List PE → List PE
  | 0, _, _, _, _, _ => []
  | n + 1, inR, L, R, sh, mg =>
    let block23 : Unit → List PE := fun _ =>
      match L with
      | l :: L' =>
        if ¬ inR l then l :: mergeOrderF n inR L' R sh mg
        else
          let L2 := if l ∈ mg then L' else L
          match R with
          | r :: R' => r :: mergeOrderF n inR L2 R' (if sh.head? = some r then sh.tail else sh) (r :: mg)
          | [] => mergeOrderF n inR L2 [] sh mg
      | [] =>
        match R with
        | r :: R' => r :: mergeOrderF n inR [] R' (if sh.head? = some r then sh.tail else sh) (r :: mg)
        | [] => []
    match L, R with
    | l :: L', r :: R' =>
      if l = r then l :: mergeOrderF n inR L' R' sh.tail (r :: mg)
      else if inR l ∧ (∃ s, sh.head? = some s ∧ s ≠ l) then mergeOrderF n inR L' R sh mg
      else block23 ()
    | _, _ => block23 ()

/-- **`mergeKeys L R`**: the keys of an associative list merged from items with keys `L` (live)
and `R` (configuration), in the merged order. -/
def mergeKeys (L R : List PE) : List PE :=
  mergeOrderF (L.length + R.length + 1) (· ∈ R) L R (R.filter (fun x => decide (x ∈ L))) []

/-- The right side wins (`ruleKeepRHS`). -/
def leafM (l r : Option UVal) : Option UVal :=
  match r with
  | some _ => r
  | none => l

/-- A list's items (`[]` for none or `null`). -/
def listItems : Option UVal → List UVal
  | some (.list vs) => vs
  | _ => []

/-- A map's entries (`[]` for none or `null`). -/
def mapItems : Option UVal → List (GoString × UVal)
  | some (.map kvs) => kvs
  | _ => []

/-- `merge`, with fuel; `none` is an absent side (Go's `nil` value). -/
def mergeF : Nat → Schema → TypeRef → Option UVal → Option UVal → Option UVal
  | 0, _, _, _, _ => none
  | n + 1, S, t, l, r =>
    match S.find t.name with
    | some (.scalar _) => leafM l r
    | some (.list e rel ks) =>
      if rel = .atomic ∨ ((listItems l).isEmpty ∧ (listItems r).isEmpty) then leafM l r else
      let ls := listItems l
      let rs := listItems r
      let out := (mergeKeys (keysOf ks ls) (keysOf ks rs)).filterMap
        (fun pe => mergeF n S e (itemOf ks ls pe) (itemOf ks rs pe))
      if out.isEmpty then none else some (.list out)
    | some (.map fs e rel) =>
      if rel = .atomic ∨ ((mapItems l).isEmpty ∧ (mapItems r).isEmpty) then leafM l r else
      let ls := mapItems l
      let rs := mapItems r
      let out := (zipLexical (ls.length + rs.length + 1) ls rs).filterMap (fun (k, a, b) =>
        match fieldType fs e k with
        | some t' => (mergeF n S t' a b).map (fun v => (k, v))
        | none => none)
      if out.isEmpty then none else some (.map out)
    | none => none

/-- **`merge S t l r`**: `r` (the configuration) merged into `l` (the live object), both of type
`t` (`TypedValue.Merge`); see the file header. -/
def merge (S : Schema) (t : TypeRef) (l r : UVal) : UVal :=
  (mergeF (l.size + r.size + 1) S t (some l) (some r)).getD .null

/-! ## Comparing -/

/-- The result of `TypedValue.Compare`. -/
structure Cmp where
  removed : PathSet
  modified : PathSet
  added : PathSet

def Cmp.none : Cmp := ⟨empty, empty, empty⟩
def Cmp.union (a b : Cmp) : Cmp :=
  ⟨a.removed.union b.removed, a.modified.union b.modified, a.added.union b.added⟩
def Cmp.unionAll (cs : List Cmp) : Cmp := cs.foldr Cmp.union Cmp.none

/-- A leaf (a scalar, an atomic value, an empty container): added, removed, or modified if the
values differ. -/
def leafC (p : Path) (l r : Option UVal) : Cmp :=
  match l, r with
  | none, _ => ⟨empty, empty, ins p⟩
  | _, none => ⟨ins p, empty, empty⟩
  | some a, some b => if a = b then Cmp.none else ⟨empty, ins p, empty⟩

/-- A container present on one side only is itself added or removed (besides its contents). -/
def nodeC (p : Path) (l r : Option UVal) : Cmp :=
  match l, r with
  | none, _ => ⟨empty, empty, ins p⟩
  | _, none => ⟨ins p, empty, empty⟩
  | _, _ => Cmp.none

/-- `compare`, with fuel. -/
def cmpF : Nat → Schema → TypeRef → Path → Option UVal → Option UVal → Cmp
  | 0, _, _, _, _, _ => Cmp.none
  | n + 1, S, t, p, l, r =>
    match S.find t.name with
    | some (.scalar _) => leafC p l r
    | some (.list e rel ks) =>
      if rel = .atomic ∨ ((listItems l).isEmpty ∧ (listItems r).isEmpty) then leafC p l r else
      let ls := listItems l
      let rs := listItems r
      let pes := keysOf ks ls ++ (keysOf ks rs).filter (fun x => decide (x ∉ keysOf ks ls))
      (Cmp.unionAll (pes.map (fun pe =>
        cmpF n S e (p ++ [pe]) (itemOf ks ls pe) (itemOf ks rs pe)))).union (nodeC p l r)
    | some (.map fs e rel) =>
      if rel = .atomic ∨ ((mapItems l).isEmpty ∧ (mapItems r).isEmpty) then leafC p l r else
      let ls := mapItems l
      let rs := mapItems r
      (Cmp.unionAll ((zipLexical (ls.length + rs.length + 1) ls rs).map (fun (k, a, b) =>
        match fieldType fs e k with
        | some t' => cmpF n S t' (p ++ [.field k]) a b
        | none => Cmp.none))).union (nodeC p l r)
    | none => Cmp.none

/-- **`compare S t l r`**: the fields removed, modified and added from `l` to `r`
(`TypedValue.Compare`). -/
def compare (S : Schema) (t : TypeRef) (l r : UVal) : Cmp :=
  cmpF (l.size + r.size + 1) S t [] (some l) (some r)

/-! ## Named fields, reconciliation -/

/-- The type of a set's child node (`SetNodeMap.EnsureNamedFieldsAreMembers`): a map's field
(or its element type), a list's keyed item; otherwise none. -/
def childType (S : Schema) (t : Option TypeRef) (pe : PE) : Option TypeRef :=
  match t.bind (fun t => S.find t.name), pe with
  | some (.map fs e _), .field n => fieldType fs e n
  | some (.list e _ _), .key _ => some e
  | _, _ => none

/-- The type at a path, as `EnsureNamedFieldsAreMembers` descends. -/
def typeAlong (S : Schema) (t : Option TypeRef) : Path → Option TypeRef
  | [] => t
  | pe :: p => typeAlong S (childType S t pe) p

/-- **`ensureNamed S t s`**: `s` and every declared field of a map type with a path of `s` below
it (`Set.EnsureNamedFieldsAreMembers`). -/
def ensureNamed (S : Schema) (t : TypeRef) (s : PathSet) : PathSet := fun q =>
  s q ∨ ∃ p n, q = p ++ [.field n] ∧ (∃ r, r ≠ [] ∧ s (q ++ r)) ∧
    ∃ fs e rel, (typeAlong S (some t) p).bind (fun t => S.find t.name) = some (.map fs e rel) ∧
      (lookupKV n fs).isSome

/-- An atomic list or map type. -/
def isAtomicT (S : Schema) (t : TypeRef) : Prop :=
  match S.find t.name with
  | some (.list _ .atomic _) => True
  | some (.map _ _ .atomic) => True
  | _ => False

/-- The type of a child as `ReconcileFieldSetWithSchema`'s walker descends (a map's key: its
field's or the element type; a list's item: the element type). -/
def reconChild (S : Schema) (t : TypeRef) (pe : PE) : Option TypeRef :=
  match S.find t.name with
  | some (.map fs e _) => match pe with
    | .field n => fieldType fs e n
    | _ => e
  | some (.list e _ _) => some e
  | _ => none

/-- The type the walker reaches a path with, through granular lists and maps only. -/
def reconAt (S : Schema) (t : TypeRef) : Path → Option TypeRef
  | [] => some t
  | pe :: p =>
    if (∃ e rel ks, S.find t.name = some (.list e rel ks) ∧ rel ≠ .atomic) ∨
       (∃ fs e rel, S.find t.name = some (.map fs e rel) ∧ rel ≠ .atomic) then
      match reconChild S t pe with
      | some t' => reconAt S t' p
      | none => none
    else none

/-- A node of `s` with paths below it, of an atomic type, reached through granular types only. -/
def atomicWithChildren (S : Schema) (t : TypeRef) (s : PathSet) (p : Path) : Prop :=
  p ≠ [] ∧ (∃ r, r ≠ [] ∧ s (p ++ r)) ∧ ∃ t', reconAt S t p = some t' ∧ isAtomicT S t'

/-- **`reconcile S t s`**: `s` with each subtree below an atomic node collapsed to that node
(`ReconcileFieldSetWithSchema`: a type changed from granular to atomic). -/
def reconcile (S : Schema) (t : TypeRef) (s : PathSet) : PathSet := fun q =>
  (s q ∧ ¬ ∃ p, atomicWithChildren S t s p ∧ p <+: q) ∨ atomicWithChildren S t s q

/-- A set written at this schema: no path below an atomic node (`reconcile` is the identity). -/
def schemaConsistent (S : Schema) (t : TypeRef) (s : PathSet) : Prop :=
  ∀ p, ¬ atomicWithChildren S t s p

/-! ## Representation predicates -/

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`isTV p sc S t x`**: the `*typed.TypedValue` at `p` holds the value `x`, of the type `t` of
the schema at `sc` (`isSchema sc S`), and `x` conforms to it (persistent). -/
def isTV (p sc : Loc) (S : Schema) (t : TypeRef) (x : UVal) : IProp GF :=
  iprop(∃ (v : value.Value) (tr : schema.TypeRef),
    p ↦□ (typed.TypedValue.mk v tr sc) ∗ isVal v x ∗ isTypeRef tr t ∗ ⌜conforms S t x⌝)

end own

end smd
end EtcdGrove
end Perennial
