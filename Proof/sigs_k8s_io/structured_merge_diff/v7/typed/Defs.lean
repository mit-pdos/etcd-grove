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

Every definition here is **computable** and branches only on decidable conditions (review round 1,
P1): `conforms` is a `Bool` computation; `ensureNamed` and `reconcile` compute their sets (their
declarative readings are laws, `Laws.lean`). So `decide` (the kernel's) evaluates them on
literals: the driver's expected results are proved that way (`Proof/.../k8s/smd/Scenario.lean`).

`isTV` carries the schema (`isSchema sc S`, `S.WF`) with the value (round 1, P2): every typed
operation takes `isTV`s, so the schema's facts need not be premises beside them.

Lean-first (2026-11-19, notes/smd-plan.md); round 1's repairs 2026-11-19.
-/
module

-- (not `typed.Base`: the package fact, `typedPools`, is over `Walkers`' predicates, so `Base`
-- imports this module's cone; Prove phase, 2026-11-19)
public import GeneratedProof.sigs_k8s_io.structured_merge_diff.v7.typed
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.strings.Base
public import Perennial.Proof.errors.Base
public import Perennial.Proof.sync.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Base
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

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
def scalarOk : Scalar → UVal → Bool
  | _, .null => true
  | .numeric, .int _ => true
  | .string, .str _ => true
  | .boolean, .bool _ => true
  | .untyped, .int _ => true
  | .untyped, .str _ => true
  | .untyped, .bool _ => true
  | _, _ => false

mutual
/-- `x` validates against the type `t` of `S` (`TypedValue.Validate`, without `AllowDuplicates`),
computed: a scalar of its kind or `null`; `null` or a list whose items conform to the element type,
for an associative list each with a key and no key twice; `null` or a map whose every key is a
declared field or, if the type has one, of the element type, its value conforming. -/
def conformsB (S : Schema) (t : TypeRef) : UVal → Bool
  | .list vs => match S.find t.name with
    | some (.list e rel ks) => conformsL S e vs &&
        (if rel = .associative then
          vs.all (fun v => (keyOf ks v).isSome) && decide (keysOf ks vs).Nodup
         else true)
    | _ => false
  | .map kvs => match S.find t.name with
    | some (.map fs e _) => conformsM S fs e kvs
    | _ => false
  | x => match S.find t.name with
    | some (.scalar s) => scalarOk s x
    | some _ => decide (x = .null)
    | none => false
/-- A list's items. -/
def conformsL (S : Schema) (e : TypeRef) : List UVal → Bool
  | [] => true
  | v :: vs => conformsB S e v && conformsL S e vs
/-- A map's entries. -/
def conformsM (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef) :
    List (GoString × UVal) → Bool
  | [] => true
  | (k, v) :: kvs => (match fieldType fs e k with
      | some t => conformsB S t v
      | none => false) && conformsM S fs e kvs
end

/-- **`conforms S t x`**: `x` validates against the type `t` of `S` (`TypedValue.Validate`; see
`conformsB`). Decidable: `decide` proves it of a literal. -/
def conforms (S : Schema) (t : TypeRef) (x : UVal) : Prop := conformsB S t x = true

instance (S : Schema) (t : TypeRef) (x : UVal) : Decidable (conforms S t x) :=
  inferInstanceAs (Decidable (_ = true))

/-! ## Field sets -/

/-- `{p}`, nothing for the root. -/
abbrev ins (p : Path) : PathSet := PathSet.single p

open PathSet in
/-- The empty set (local shorthand). -/
abbrev empty : PathSet := PathSet.empty
/-- Union (local shorthand). -/
abbrev union (a b : PathSet) : PathSet := PathSet.union a b

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
      if [pe] ∈ R then removeL S e ks R vs
      else if ¬ (R.under pe).IsEmpty then removeAt S e (R.under pe) v :: removeL S e ks R vs
      else v :: removeL S e ks R vs
    | none => v :: removeL S e ks R vs
/-- A map's entries, likewise. -/
def removeM (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef) (R : PathSet) :
    List (GoString × UVal) → List (GoString × UVal)
  | [] => []
  | (k, v) :: kvs =>
    if [.field k] ∈ R then removeM S fs e R kvs
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
def mergeOrderF : Nat → (PE → Bool) → List PE → List PE → List PE → List PE → List PE
  | 0, _, _, _, _, _ => []
  | n + 1, inR, L, R, sh, mg =>
    let block23 : Unit → List PE := fun _ =>
      match L with
      | l :: L' =>
        if !inR l then l :: mergeOrderF n inR L' R sh mg
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
      else if inR l && (match sh.head? with
          | some s => decide (s ≠ l)
          | none => false) then mergeOrderF n inR L' R sh mg
      else block23 ()
    | _, _ => block23 ()

/-- **`mergeKeys L R`**: the keys of an associative list merged from items with keys `L` (live)
and `R` (configuration), in the merged order. -/
def mergeKeys (L R : List PE) : List PE :=
  mergeOrderF (L.length + R.length + 1) (fun x => decide (x ∈ R)) L R
    (R.filter (fun x => decide (x ∈ L))) []

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

instance : DecidableEq Cmp := fun a b =>
  decidable_of_iff (a.removed = b.removed ∧ a.modified = b.modified ∧ a.added = b.added) (by
    cases a; cases b; simp only [Cmp.mk.injEq])

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

/-! ## Reconciliation (the named fields along paths, `ensureNamed`, are `fieldpath`'s:
`fieldpath/NamedVocab.lean`) -/

/-- An atomic list or map type. -/
def isAtomicT (S : Schema) (t : TypeRef) : Bool :=
  match S.find t.name with
  | some (.list _ .atomic _) => true
  | some (.map _ _ .atomic) => true
  | _ => false

/-- The type of a child as `ReconcileFieldSetWithSchema`'s walker descends (a map's key: its
field's or the element type; a list's item: the element type). -/
def reconChild (S : Schema) (t : TypeRef) (pe : PE) : Option TypeRef :=
  match S.find t.name with
  | some (.map fs e _) => match pe with
    | .field n => fieldType fs e n
    | _ => e
  | some (.list e _ _) => some e
  | _ => none

/-- A granular (not atomic) list or map type. -/
def isGranularT (S : Schema) (t : TypeRef) : Bool :=
  match S.find t.name with
  | some (.list _ rel _) => decide (rel ≠ .atomic)
  | some (.map _ _ rel) => decide (rel ≠ .atomic)
  | _ => false

/-- The type the walker reaches a path with, through granular lists and maps only. -/
def reconAt (S : Schema) (t : TypeRef) : Path → Option TypeRef
  | [] => some t
  | pe :: p =>
    if isGranularT S t then
      match reconChild S t pe with
      | some t' => reconAt S t' p
      | none => none
    else none

/-- The strict prefixes of a path. -/
def strictPrefixes : Path → List Path
  | [] => []
  | e :: r => [] :: (strictPrefixes r).map (e :: ·)

/-- **The atomic nodes with children** of `s`: the non-empty paths `p` with a path of `s` strictly
below them (`p ++ r ∈ s`, `r ≠ []`), whose type, reached through granular types only, is atomic
(`ReconcileFieldSetWithSchema`: a type changed from granular to atomic). -/
def atomicNodes (S : Schema) (t : TypeRef) (s : PathSet) : PathSet :=
  (s.bind strictPrefixes).filter (fun p => !p.isEmpty && match reconAt S t p with
    | some t' => isAtomicT S t'
    | none => false)

/-- **`reconcile S t s`**: `s` with each subtree below an atomic node collapsed to that node
(`ReconcileFieldSetWithSchema`): the paths of `s` with no atomic node with children as a prefix
(themselves included), and those nodes. -/
def reconcile (S : Schema) (t : TypeRef) (s : PathSet) : PathSet :=
  let ns := atomicNodes S t s
  FSet.union (s.filter (fun q => !ns.any (fun p => p.isPrefixOf q))) ns

/-- A set written at this schema: no path below an atomic node (`reconcile` is the identity:
`reconcile_id`). Decidable. -/
def schemaConsistent (S : Schema) (t : TypeRef) (s : PathSet) : Prop :=
  (atomicNodes S t s).isEmpty = true

instance (S : Schema) (t : TypeRef) (s : PathSet) : Decidable (schemaConsistent S t s) :=
  inferInstanceAs (Decidable (_ = true))

/-! ## Representation predicates -/

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`isTV p sc S t x`**: the `*typed.TypedValue` at `p` holds the value `x`, of the type `t` of
the schema at `sc`, which holds `S` (`isSchema sc S`), a schema in scope (`S.WF`), and `x`
conforms to `t` (persistent). Sealed: `isTV_conforms`, `isTV_schema` give its facts. -/
@[no_expose] def isTV (p sc : Loc) (S : Schema) (t : TypeRef) (x : UVal) : IProp GF :=
  iprop(∃ (v : value.Value) (tr : schema.TypeRef),
    p ↦□ (typed.TypedValue.mk v tr sc) ∗ isVal v x ∗ isTypeRef tr t ∗ isSchema sc S ∗
    ⌜S.WF ∧ conforms S t x⌝)

end own

end smd
end EtcdGrove
end Perennial
