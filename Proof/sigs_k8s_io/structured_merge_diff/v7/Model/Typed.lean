/-
The pure model of SMD's **typed values** (`typed` package): the walkers (`Validate`,
`ToFieldSet`, `Merge` with `ruleKeepRHS`, `Compare`, `RemoveItems` without extraction,
`ReconcileFieldSetWithSchema`) and the helpers they call (`deduceAtom`, `handleAtom`,
`validateScalar`, `listItemToPathElement`, ...), and `TV` (a `*typed.TypedValue`).

Each walker is one function with fuel (the wrappers give the values' `size + 1`, more than the
depth), its `handleAtom` cases inline, its loops as folds; a walker's errors are a `Bool`
(whether its `ValidationErrors` is non-empty: the callers only test that). Go iterates over a Go
map in an unspecified order; the model iterates in key order, which is unobservable in these
walkers (their results are maps, sets built by insertion, and error flags). Quirks of the Go
code kept: `mergingWalker.visitListItems` drops the list items' errors (`mergeOut, errs :=
w.mergeListItem(...)` shadows `errs`); `RemoveItems` turns a map or list it empties into `null`;
`ToFieldSet` ignores `listItemToPathElement`'s errors (a zero `PathElement`, `PE.invalid`).

Lean-first (2026-11-19, notes/smd-robustness.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.Model.Fieldpath

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace smd

/-! ## typed -/

/-- `typed.deduceAtom` (`none`: a nil `value.Value`). -/
def deduceAtom (a : Atom) : Option UVal → Atom
  | none => a
  | some (.int _) | some (.str _) | some (.bool _) =>
    match a.scalar with | some s => .ofScalar s | none => a
  | some (.list _) => match a.list with | some l => .ofList l | none => a
  | some (.map _) => match a.map with | some m => .ofMap m | none => a
  | some .null => a

/-- What `typed.handleAtom` dispatches to. -/
inductive Handled where
  | map (m : MapT) | scalar (s : GoString) | list (l : ListT) | invalid

def handleAtom (a : Atom) : Handled :=
  match a.map, a.scalar, a.list with
  | some m, _, _ => .map m
  | none, some s, _ => .scalar s
  | none, none, some l => .list l
  | none, none, none => .invalid

/-- `typed.validateScalar` (`true`: an error). -/
def validateScalar (t : GoString) : Option UVal → Bool
  | none => false
  | some .null => false
  | some v =>
    if t = go!"numeric" then !v.isInt
    else if t = go!"string" then !v.isString
    else if t = go!"boolean" then !v.isBool
    else if t = go!"untyped" then !(v.isInt || v.isString || v.isBool)
    else true

/-- `getAssociativeKeyDefault`'s outcome (no defaults): `none` an error, `some ()` no default. -/
def assocKeyDefault (sc : Schema) (l : ListT) : Option Unit :=
  match sc.resolve l.elementType with
  | none => none
  | some a => if a.map.isNone then none else some ()

/-- `keyedAssociativeListItemToPathElement` (`none`: an error). -/
def keyedItemToPE (sc : Schema) (l : ListT) (child : UVal) : Option PE :=
  match child with
  | .map kvs =>
    let step : Option FieldList → GoString → Option FieldList := fun acc k =>
      match acc with
      | none => none
      | some fl => match lookupKV k kvs with
        | some v => some (fl ++ [(k, v)])
        | none => match assocKeyDefault sc l with | none => none | some () => some fl
    match l.keys.foldl step (some []) with
    | none => none
    | some fl => if !l.keys.isEmpty && fl.isEmpty then none else some (.key (flSort fl))
  | _ => none

/-- `setItemToPathElement`. -/
def setItemToPE (child : UVal) : Option PE :=
  match child with
  | .map _ | .list _ | .null => none
  | v => some (.value v)

/-- `listItemToPathElement` (`none`: an error). -/
def listItemToPE (sc : Schema) (l : ListT) (child : UVal) : Option PE :=
  if l.er ≠ erAssociative then none
  else if !l.keys.isEmpty then keyedItemToPE sc l child
  else setItemToPE child

/-- `listValue`/`mapValue` with the error ignored (`derefList`, `derefMap`, the walkers'
`list, _ :=`): the items, or `none` for nil (a nil value, `null`, or another kind). -/
def derefList : Option UVal → Option (List UVal)
  | some (.list vs) => some vs
  | _ => none
def derefMap : Option UVal → Option (List (GoString × UVal))
  | some (.map kvs) => some kvs
  | _ => none

/-- `MapZip(..., Unordered, ...)`: every key of either map with each side's value (here in
lexical order; the walkers' results do not depend on it). -/
def zipMaps (l r : Option (List (GoString × UVal))) : List (GoString × Option UVal × Option UVal) :=
  let as := l.getD []
  let bs := r.getD []
  UVal.zipLexical (as.length + bs.length + 1) as bs

/-- The field's type of a map's key: the field's, else the element type. -/
def MapT.fieldType (t : MapT) (k : GoString) : TypeRef :=
  match t.findField k with | some f => f.type | none => t.elementType

/-! ### `Validate` (`validatingObjectWalker`, no `AllowDuplicates`): `true` an error -/

def validateW : Nat → Schema → TypeRef → UVal → Bool
  | 0, _, _, _ => true
  | n + 1, sc, tr, v =>
    match sc.resolve tr with
    | none => true
    | some a =>
      match handleAtom (deduceAtom a (some v)) with
      | .scalar t => validateScalar t (some v)
      | .list t =>
        match v with
        | .null => false
        | .list items =>
          -- `visitListItems`
          let step : (Bool × Bool × List PE × Nat) → UVal → (Bool × Bool × List PE × Nat) :=
            fun (errs, stop, seen, i) child =>
              if stop then (errs, stop, seen, i + 1) else
              let pe? : Option PE :=
                if t.er ≠ erAssociative then some (.index (BitVec.ofNat 64 i)) else listItemToPE sc t child
              match pe? with
              | none => (true, true, seen, i + 1)
              | some pe =>
                let dup := t.er = erAssociative && pesHas pe seen
                let seen := if t.er = erAssociative then pesInsert pe seen else seen
                (errs || dup || validateW n sc t.elementType child, false, seen, i + 1)
          (items.foldl step (false, false, [], 0)).1
        | _ => true
      | .map t =>
        match v with
        | .null => false
        | .map kvs =>
          kvs.any (fun (k, val) =>
            match t.findField k with
            | some f => validateW n sc f.type val
            | none => if t.elementType.isZero then true else validateW n sc t.elementType val)
        | _ => true
      | .invalid => true

/-- `TypedValue.Validate()`: `true` an error. -/
def validate (sc : Schema) (tr : TypeRef) (v : UVal) : Bool := validateW (v.size + 1) sc tr v

/-! ### `ToFieldSet` (`toFieldSetWalker`) -/

/-- The walker at `path` over `v` (`none`: a nil value), adding to `acc`; `true`: an error. -/
def toFieldSetW : Nat → Schema → Path → TypeRef → Option UVal → PSet → PSet × Bool
  | 0, _, _, _, _, acc => (acc, true)
  | n + 1, sc, path, tr, v, acc =>
    match sc.resolve tr with
    | none => (acc, true)
    | some a =>
      match handleAtom (deduceAtom a v) with
      | .scalar _ => (acc.insert path, false)
      | .list t =>
        let list := derefList v
        if t.er = erAtomic then (acc.insert path, false) else
        match list with
        | none => (acc, false)
        | some items =>
          let pes := items.map (fun c => ((listItemToPE sc t c).getD .invalid, c))
          -- first pass: the duplicates' paths
          let (_, dups, acc) := pes.foldl (fun (seen, dups, acc) (pe, _) =>
            if pesHas pe seen then
              if pesHas pe dups then (seen, dups, acc) else (seen, pesInsert pe dups, acc.insert (path ++ [pe]))
            else (pesInsert pe seen, dups, acc)) (([] : List PE), ([] : List PE), acc)
          -- second pass: the other items
          pes.foldl (fun (acc, errs) (pe, c) =>
            if pesHas pe dups then (acc, errs) else
            let (acc, e) := toFieldSetW n sc (path ++ [pe]) t.elementType (some c) acc
            (acc.insert (path ++ [pe]), errs || e)) (acc, false)
      | .map t =>
        let m := derefMap v
        if t.er = erAtomic then (acc.insert path, false) else
        match m with
        | none => (acc, false)
        | some kvs =>
          kvs.foldl (fun (acc, errs) (k, val) =>
            let p := path ++ [PE.field k]
            let (acc, e) := toFieldSetW n sc p (t.fieldType k) (some val) acc
            let acc :=
              if val.isNull || (match val with | .map kvs' => kvs'.isEmpty | _ => false) then acc.insert p
              else if (t.findField k).isNone then acc.insert p
              else acc
            (acc, errs || e)) (acc, false)
      | .invalid => (acc, true)

/-! ### `Merge` (`mergingWalker` with `ruleKeepRHS`) -/

/-- `PathElementValueMap`: sorted by `PathElement.Compare`. -/
def pevGet (pe : PE) : List (PE × UVal) → Option UVal
  | [] => none
  | (a, v) :: rest => let c := a.compare pe; if c < 0 then pevGet pe rest else if c == 0 then some v else none
def pevInsert (pe : PE) (v : UVal) : List (PE × UVal) → List (PE × UVal)
  | [] => [(pe, v)]
  | (a, w) :: rest =>
    let c := a.compare pe
    if c < 0 then (a, w) :: pevInsert pe v rest else if c == 0 then (a, v) :: rest
    else (pe, v) :: (a, w) :: rest

/-- `mergingWalker.indexListPathElements`: the items' path elements (with the items), the
observed map, whether there was an error. -/
def mergeIndex (sc : Schema) (t : ListT) (items : List UVal) (allowDup : Bool) :
    List (PE × UVal) × List (PE × UVal) × Bool :=
  items.foldl (fun (pes, obs, errs) child =>
    match listItemToPE sc t child with
    | none => (pes, obs, true)
    | some pe =>
      match pevGet pe obs with
      | some _ =>
        if !allowDup then (pes, obs, true) else (pes ++ [(pe, child)], pevInsert pe .null obs, errs)
      | none => (pes ++ [(pe, child)], pevInsert pe child obs, errs)) ([], [], false)

/-- `mergingWalker.visitListItems`'s loop, with fuel; `item pe l r` merges one item. The state:
the lhs path elements left (with their items), the rhs ones left, `mergedRHS`, `nextShared`,
`sharedOrder`, `out`. -/
def mergeListLoop (item : PE → Option UVal → Option UVal → Option UVal)
    (obsL obsR : List (PE × UVal)) :
    Nat → List (PE × UVal) → List PE → List PE → Option PE → List PE → List UVal → List UVal
  | 0, _, _, _, _, _, out => out
  | _ + 1, [], [], _, _, _, out => out
  | n + 1, ls, rs, merged, next, shared, out =>
    let pop : List PE → Option PE × List PE := fun s => match s with | [] => (none, []) | x :: xs => (some x, xs)
    let app : List UVal → Option UVal → List UVal := fun out o => match o with | some v => out ++ [v] | none => out
    -- the rest of the body: `if lI < lLen { ... }` then `if rI < rLen { ... }`
    let lhsThenRhs : List (PE × UVal) → List UVal → List UVal := fun ls out =>
      match ls with
      | (pe, c) :: ls' =>
        if (pevGet pe obsR).isNone then
          mergeListLoop item obsL obsR n ls' rs merged next shared (app out (item pe (some c) none))
        else
          let ls := if pesHas pe merged then ls' else ls
          match rs with
          | r :: rs' =>
            let out := app out (item r (pevGet r obsL) (pevGet r obsR))
            let (next, shared) := match next with
              | some x => if x.equals r then pop shared else (next, shared)
              | none => (next, shared)
            mergeListLoop item obsL obsR n ls rs' (pesInsert r merged) next shared out
          | [] => mergeListLoop item obsL obsR n ls rs merged next shared out
      | [] =>
        match rs with
        | r :: rs' =>
          let out := app out (item r (pevGet r obsL) (pevGet r obsR))
          let (next, shared) := match next with
            | some x => if x.equals r then pop shared else (next, shared)
            | none => (next, shared)
          mergeListLoop item obsL obsR n ls rs' (pesInsert r merged) next shared out
        | [] => out
    match ls, rs with
    | (pe, _) :: ls', r :: rs' =>
      if pe.equals r then
        let out := app out (item pe (pevGet pe obsL) (pevGet pe obsR))
        let (next, shared) := pop shared
        mergeListLoop item obsL obsR n ls' rs' (pesInsert pe merged) next shared out
      else if (pevGet pe obsR).isSome && (match next with | some x => !x.equals pe | none => false) then
        mergeListLoop item obsL obsR n ls' rs merged next shared out
      else lhsThenRhs ls out
    | _, _ => lhsThenRhs ls out

/-- The merging walker at `path`: its output (`none`: `w.out` nil) and whether there was an
error. -/
def mergeW : Nat → Schema → Path → TypeRef → Option UVal → Option UVal → Option UVal × Bool
  | 0, _, _, _, _, _ => (none, true)
  | n + 1, sc, path, tr, lhs, rhs =>
    if lhs.isNone && rhs.isNone then (none, true) else
    match sc.resolve tr with
    | none => (none, true)
    | some a =>
      let alhs := deduceAtom a lhs
      let arhs := deduceAtom a rhs
      -- `handleAtom` on one walker (`lhs`, `rhs` as given): (out, errors)
      let leaf : Option UVal := match rhs with | some r => some r | none => lhs
      let handle (at0 : Atom) : Option UVal × Bool :=
        match handleAtom at0 with
        | .scalar t =>
          if validateScalar t lhs && validateScalar t rhs then (none, true) else (leaf, false)
        | .list t =>
          let l := derefList lhs
          let r := derefList rhs
          let emptyPromote := (l.getD []).isEmpty && (r.getD []).isEmpty
          if t.er = erAtomic || emptyPromote then (leaf, false) else
          -- `visitListItems`
          let (rPEs, obsR, rErrs) := mergeIndex sc t (r.getD []) false
          let (lPEs, obsL, lErrs) := mergeIndex sc t (l.getD []) true
          if rErrs || lErrs then (none, true) else
          let rPEs := rPEs.map (·.1)
          let shared := rPEs.filter (fun pe => (pevGet pe obsL).isSome)
          let (next, shared) := match shared with | [] => (none, []) | x :: xs => (some x, xs)
          let item : PE → Option UVal → Option UVal → Option UVal := fun pe l r =>
            -- `mergeListItem`: the item's errors are dropped (`errs` shadowed)
            (mergeW n sc (path ++ [pe]) t.elementType l r).1
          let out := mergeListLoop item obsL obsR (lPEs.length + rPEs.length + 1) lPEs rPEs [] next shared []
          (if out.isEmpty then none else some (.list out), false)
        | .map t =>
          let l := derefMap lhs
          let r := derefMap rhs
          let emptyPromote := (l.getD []).isEmpty && (r.getD []).isEmpty
          if t.er = erAtomic || emptyPromote then (leaf, false) else
          let (out, errs) := (zipMaps l r).foldl (fun (out, errs) (k, lv, rv) =>
            let (o, e) := mergeW n sc (path ++ [PE.field k]) (t.fieldType k) lv rv
            (match o with | some v => insertKV k v out | none => out, errs || e)) ([], false)
          (if out.isEmpty then none else some (.map out), errs)
        | .invalid => (none, true)
      if rhs.isNone then handle alhs
      else if lhs.isNone || Atom.equals alhs arhs then handle arhs
      else
        let (_, e1) := handle alhs
        let (o, e2) := handle arhs
        (o, e1 || e2)

/-! ### `Compare` (`compareWalker`) -/

structure Comparison where
  removed : PSet
  modified : PSet
  added : PSet
  deriving Inhabited

def Comparison.empty : Comparison := ⟨.empty, .empty, .empty⟩

/-- `PathElementMap` of lists of items: sorted by `PathElement.Compare`. -/
def pelGet (pe : PE) : List (PE × List UVal) → Option (List UVal)
  | [] => none
  | (a, v) :: rest => let c := a.compare pe; if c < 0 then pelGet pe rest else if c == 0 then some v else none
def pelInsert (pe : PE) (v : List UVal) : List (PE × List UVal) → List (PE × List UVal)
  | [] => [(pe, v)]
  | (a, w) :: rest =>
    let c := a.compare pe
    if c < 0 then (a, w) :: pelInsert pe v rest else if c == 0 then (a, v) :: rest
    else (pe, v) :: (a, w) :: rest

/-- The comparing walker at `path`, adding to `c`; `true`: an error. -/
def compareW : Nat → Schema → Path → TypeRef → Option UVal → Option UVal → Comparison → Comparison × Bool
  | 0, _, _, _, _, _, c => (c, true)
  | n + 1, sc, path, tr, lhs, rhs, c =>
    if lhs.isNone && rhs.isNone then (c, true) else
    match sc.resolve tr with
    | none => (c, true)
    | some a =>
      let alhs := deduceAtom a lhs
      let arhs := deduceAtom a rhs
      -- `doLeaf`
      let leaf (c : Comparison) : Comparison :=
        match lhs, rhs with
        | none, _ => { c with added := c.added.insert path }
        | _, none => { c with removed := c.removed.insert path }
        | some l, some r => if !UVal.equals r l then { c with modified := c.modified.insert path } else c
      -- `handleAtom` on one walker: (comparison, inLeaf, errors)
      let handle (at0 : Atom) (c : Comparison) : Comparison × Bool × Bool :=
        match handleAtom at0 with
        | .scalar t =>
          if validateScalar t lhs && validateScalar t rhs then (c, false, true) else (leaf c, true, false)
        | .list t =>
          let l := derefList lhs
          let r := derefList rhs
          let emptyPromote := (l.getD []).isEmpty && (r.getD []).isEmpty
          if t.er = erAtomic || emptyPromote then (leaf c, true, false) else
          -- `visitListItems`
          let index (items : List UVal) (lvals : List (PE × List UVal)) (forR : Bool)
              (st : List (PE × List UVal) × List PE × Bool) :=
            items.foldl (fun (vals, all, errs) child =>
              match listItemToPE sc t child with
              | none => (vals, all, true)
              | some pe =>
                match pelGet pe vals with
                | some vs => (pelInsert pe (vs ++ [child]) vals, all, errs)
                | none =>
                  let all := if !forR || (pelGet pe lvals).isNone then all ++ [pe] else all
                  (pelInsert pe [child] vals, all, errs)) st
          let (lVals, allPEs, lErrs) := index (l.getD []) [] false ([], [], false)
          let (rVals, allPEs, rErrs) := index (r.getD []) lVals true ([], allPEs, false)
          let item (pe : PE) (lv rv : Option UVal) (c : Comparison) : Comparison × Bool :=
            compareW n sc (path ++ [pe]) t.elementType lv rv c
          let (c, errs, _) := allPEs.foldl (fun (c, errs, stop) pe =>
            if stop then (c, errs, stop) else
            let lList := (pelGet pe lVals).getD []
            let rList := (pelGet pe rVals).getD []
            if lList.isEmpty && rList.isEmpty then (c, errs, true)
            else if lList.length ≤ 1 && rList.length ≤ 1 then
              let (c, e) := item pe lList.head? rList.head? c
              (c, errs || e, false)
            else if lList.length ≥ 2 && rList.length ≥ 2 then
              let eq := lList.length == rList.length && (lList.zip rList).all (fun (a, b) => UVal.equals a b)
              (if !eq then { c with modified := c.modified.insert (path ++ [pe]) } else c, errs, false)
            else if lList.length ≥ 2 then
              let (c, e) := if rList.isEmpty then (c, false) else item pe none rList.head? c
              ({ c with removed := c.removed.insert (path ++ [pe]) }, errs || e, false)
            else
              let (c, e) := if lList.isEmpty then (c, false) else item pe lList.head? none c
              ({ c with added := c.added.insert (path ++ [pe]) }, errs || e, false)) (c, lErrs || rErrs, false)
          (c, false, errs)
        | .map t =>
          let l := derefMap lhs
          let r := derefMap rhs
          let emptyPromote := (l.getD []).isEmpty && (r.getD []).isEmpty
          if t.er = erAtomic || emptyPromote then (leaf c, true, false) else
          let (c, errs) := (zipMaps l r).foldl (fun (c, errs) (k, lv, rv) =>
            let (c, e) := compareW n sc (path ++ [PE.field k]) (t.fieldType k) lv rv c
            (c, errs || e)) (c, false)
          (c, false, errs)
        | .invalid => (c, false, true)
      let (c, inLeaf, errs) :=
        if rhs.isNone then handle alhs c
        else if lhs.isNone || Atom.equals alhs arhs then handle arhs c
        else
          let (c, _, e1) := handle alhs c
          let (c, inLeaf, e2) := handle arhs c
          (c, inLeaf, e1 || e2)
      let c :=
        if inLeaf then c
        else if lhs.isNone then { c with added := c.added.insert path }
        else if rhs.isNone then { c with removed := c.removed.insert path }
        else c
      (c, errs)

/-! ### `RemoveItems` (`removingWalker`, not extracting) -/

/-- `removeItemsWithSchema(val, toRemove, schema, typeRef, false)`: `w.out` (`null` if nil). -/
def removeW : Nat → Schema → UVal → PSet → TypeRef → UVal
  | 0, _, _, _, _ => .null
  | n + 1, sc, v, toRemove, tr =>
    match sc.resolve tr with
    | none => .null
    | some a =>
      match handleAtom (deduceAtom a (some v)) with
      | .scalar _ => v
      | .list t =>
        match v with
        | .list items =>
          if items.isEmpty || t.er = erAtomic then .null else
          let newItems := items.foldl (fun acc item =>
            let pe := (listItemToPE sc t item).getD .invalid
            if toRemove.has [pe] then acc
            else
              let sub := toRemove.withPrefix pe
              acc ++ [if !sub.isEmpty then removeW n sc item sub t.elementType else item]) []
          if newItems.isEmpty then .null else .list newItems
        | _ => .null
      | .map t =>
        match v with
        | .map kvs =>
          if kvs.isEmpty || t.er = erAtomic then .null else
          -- `fieldTypes`: the last field of a name
          let fieldType (k : GoString) : TypeRef :=
            match t.findField k with | some f => f.type | none => t.elementType
          let newMap := kvs.foldl (fun acc (k, val) =>
            if toRemove.has [PE.field k] then acc
            else
              let sub := toRemove.withPrefix (PE.field k)
              insertKV k (if !sub.isEmpty then removeW n sc val sub (fieldType k) else val) acc) []
          if newMap.isEmpty then .null else .map newMap
        | _ => .null
      | .invalid => .null

/-! ### `ReconcileFieldSetWithSchema` (`reconcileWithSchemaWalker`) -/

/-- `isUntypedDeducedMap` (`Fields == nil`: no fields). -/
def isUntypedDeducedMap (t : MapT) : Bool :=
  let ref := t.elementType
  let untyped := match ref.namedType with
    | some n => decide (n = go!"__untyped_deduced_")
    | none => ref.inlined.scalar == some go!"untyped"
  untyped && t.fields.isEmpty

/-- `typeRefAtPath`. -/
def typeRefAtPath (t : MapT) (pe : PE) : Option TypeRef :=
  let tr := match pe with
    | .field n => match t.findField n with | some f => f.type | none => t.elementType
    | _ => t.elementType
  if tr.isZero then none else some tr

/-- The walker at `path` over the field set `fs` (`none`: nil): the paths of atomic types
found granular (`toRemove`, `toAdd`), whether there was an error. -/
def reconcileW : Nat → Schema → Option PSet → Path → TypeRef → Bool → List Path × Bool
  | 0, _, _, _, _, _ => ([], true)
  | n + 1, sc, fs, path, tr, isAtomic =>
    match sc.resolve tr with
    | none => ([], true)
    | some a =>
      let visit (s : PSet) (tyOf : PE → Option TypeRef) : List Path × Bool :=
        let handle (acc : List Path × Bool) (pe : PE) (isMember : Bool) : List Path × Bool :=
          match tyOf pe with
          | none => acc
          | some tr' =>
            let sub := PSet.nodeGet pe s.children
            let (ps, e) := reconcileW n sc sub (path ++ [pe]) tr' (isMember && sub.isNone)
            (acc.1 ++ ps, acc.2 || e)
        let acc := s.children.foldl (fun acc (pe, _) =>
          if pesHas pe s.members then acc else handle acc pe false) ([], false)
        s.members.foldl (fun acc pe => handle acc pe true) acc
      match handleAtom a with
      | .map t =>
        if isUntypedDeducedMap t then ([], false)
        else if !isAtomic && t.er = erAtomic then
          match fs with
          | some s => if s.size > 0 then ([path], false) else ([], false)
          | none => ([], false)
        else match fs with
          | some s => visit s (typeRefAtPath t)
          | none => ([], false)
      | .scalar _ => ([], false)
      | .list t =>
        if !isAtomic && t.er = erAtomic then ([path], false)
        else match fs with
          | some s => visit s (fun _ => some t.elementType)
          | none => ([], false)
      | .invalid => ([], true)

/-- `ReconcileFieldSetWithSchema(fs, tv)`: `none` an error, `some none` nothing to change. -/
def reconcileFieldSet (sc : Schema) (fs : PSet) (tr : TypeRef) : Option (Option PSet) :=
  let fuel := fs.weight + 1
  let (ps, errs) := reconcileW (fuel + 1) sc (some fs) [] tr false
  if errs then none
  else if ps.isEmpty then some none
  else some (some ((fs.rdiff (PSet.ofPaths ps)).union (PSet.ofPaths ps)))

/-! ### `TypedValue` -/

/-- A `typed.TypedValue` (its schema is the one of the call; `value` `none`: a nil
`value.Value`). -/
structure TV where
  value : Option UVal
  typeRef : TypeRef

instance : Inhabited TV := ⟨⟨none, default⟩⟩

def fuelOf (v : Option UVal) : Nat := match v with | some v => v.size | none => 0

/-- `typed.AsTyped(v, s, typeRef)`: `none` a validation error. -/
def asTyped (sc : Schema) (v : UVal) (tr : TypeRef) : Option TV :=
  if validate sc tr v then none else some ⟨some v, tr⟩

/-- `TypedValue.ToFieldSet`: `none` an error, `some none` a panic (a nil value of a list
type). -/
def tvToFieldSet (sc : Schema) (tv : TV) : Option (Option PSet) :=
  match tv.value with
  | some v => let (s, e) := toFieldSetW (v.size + 1) sc [] tv.typeRef (some v) .empty
    if e then none else some (some s)
  | none =>
    match sc.resolve tv.typeRef with
    | none => none
    | some a => match handleAtom a with
      | .list _ => some none
      | .invalid => none
      | _ => some (some .empty)

/-- `TypedValue.Merge` (`typed.merge` with `ruleKeepRHS`): `none` an error. -/
def tvMerge (sc : Schema) (lhs rhs : TV) : Option TV :=
  if !lhs.typeRef.equals rhs.typeRef then none else
  let (out, e) := mergeW (fuelOf lhs.value + fuelOf rhs.value + 1) sc [] lhs.typeRef lhs.value rhs.value
  if e then none else some ⟨out, lhs.typeRef⟩

/-- `TypedValue.Compare`: `none` an error. -/
def tvCompare (sc : Schema) (lhs rhs : TV) : Option Comparison :=
  if !lhs.typeRef.equals rhs.typeRef then none else
  let (c, e) := compareW (fuelOf lhs.value + fuelOf rhs.value + 1) sc [] lhs.typeRef lhs.value rhs.value .empty
  if e then none else some c

/-- `TypedValue.RemoveItems`: `none` a panic (a nil value). -/
def tvRemoveItems (sc : Schema) (tv : TV) (s : PSet) : Option TV :=
  match tv.value with
  | some v => some ⟨some (removeW (v.size + 1) sc v s tv.typeRef), tv.typeRef⟩
  | none =>
    match sc.resolve tv.typeRef with
    | none => some ⟨some .null, tv.typeRef⟩
    | some a => match handleAtom a with
      | .invalid => some ⟨some .null, tv.typeRef⟩
      | _ => none

end smd
end EtcdGrove
end Perennial
