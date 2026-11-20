/-
**The `typed` package's walkers, their state and invariants** (structured-merge-diff v7.0.0): the
vocabulary of the per-function specs of `typed` beyond `Defs.lean` (`notes/smd-plan.md`, "The
call DAG", the `typed` rows). Draft (2026-11-19): definitions written in full, laws stated
(`WalkerLaws.lean`), nothing proved.

**What a walker is.** Each of SMD's typed operations walks a value (or two, or a field set) with
a mutable struct, one per level of the descent: `mergingWalker` (`Merge`), `compareWalker`
(`Compare`), `toFieldSetWalker` (`ToFieldSet`), `validatingObjectWalker` (`Validate`),
`reconcileWithSchemaWalker` (`ReconcileFieldSetWithSchema`), `removingWalker` (`RemoveItems`).
A walker at a node knows the node's type (`TypeRef`), its path, the value(s) there, and builds an
output (the merged value, the comparison's three sets, the field set, the paths to collapse). The
top walker comes from a `sync.Pool`; a descent takes a child walker from the spare list the
walkers of one traversal share (`spareWalkers`), fills it from the parent (`*w2 = *w`), runs it,
and puts it back (`finishDescent`).

**The invariants**, per walker `X` (`mw`, `cw`, `tw`, `vw`, `rw`; the removing walker has no
descent):
- `XCore w … st (ps sp a)`: the walker's struct at `w` (owned) with the state `st` (its node's
  type, path, values and flags, a record of pure values) and the schema it reads (`isSchema`,
  `S.WF`); `ps` its path slice, `sp` its spare list, `a` its allocator. During a descent the
  parent keeps only its `XCore` (frozen): the child runs with the resources.
- `XOwn w … st`: the active walker: its `XCore` with the resources a descent hands from parent to
  child and back: the path buffer (`ownPath`), the spare walkers (`spareWalkers`), the allocator
  (`isAlloc`), and the output under construction (the comparison's sets, the field set: owned).
- `XPooled w`: what a walker the pool holds keeps (its path buffer emptied, its spare list, its
  allocator): the pool's predicate (`typedPools`).
The values a walker visits are **not** in its state's resources: they are lent with the call
(`isValO v dq x`, any share: `MapZipUsing` lends each entry's wrapper whole and reuses it), so a
walker method's spec takes and gives them back.

**What each walker method contributes**, in the pure operations' terms (`Defs.lean`) at its node:
`mergingWalker` sets its `out` to `mergeO S t l r` (`mergeF` at the node); `compareWalker` adds
`cmpO S t p l r` to the comparison; `toFieldSetWalker` adds `fieldsAt S t p x` to the set;
`validatingObjectWalker` returns no error iff `conforms S t x`; `reconcileWithSchemaWalker` adds
the atomic nodes with children below its node (`reconOut`); `removingWalker` sets its `out` to
`removeAt S t R x`. The `TypedValue` methods are glue over these.

The package fact (`typedPools`: the pools' `isPool`s and `ruleKeepRHS`'s closure) is what
`Base.lean`'s `isPkgInit typed` must become (today `True`; `etc/gen-init.py`'s `SPECIAL` must
prove it at initialization): `typedPkgInit_pools.law` (`WalkerLaws.lean`).

Draft (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.Defs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Objects
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.NamedVocab
public import Perennial.Proof.sync.PoolDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

/-! ## Pure helpers -/

/-- The size of a side that may be absent. -/
def sizeO : Option UVal → Nat
  | none => 0
  | some x => x.size

/-- Fuel enough for `mergeF`/`cmpF` on two sides. -/
def fuelO (l r : Option UVal) : Nat := sizeO l + sizeO r + 1

/-- **`mergeO S t l r`**: what the merging walker's `out` is after merging the sides `l`, `r`
(`none`: an absent side, Go's nil `Value`) at a node of type `t`: `mergeF` with enough fuel
(`merge S t l r = (mergeO S t (some l) (some r)).getD .null`, `merge_mergeO`). -/
def mergeO (S : Schema) (t : TypeRef) (l r : Option UVal) : Option UVal :=
  mergeF (fuelO l r) S t l r

/-- **`cmpO S t p l r`**: what the compare walker adds at the node of path `p`, type `t`
(`compare S t l r = cmpO S t [] (some l) (some r)`). -/
def cmpO (S : Schema) (t : TypeRef) (p : Path) (l r : Option UVal) : Cmp :=
  cmpF (fuelO l r) S t p l r

/-- A side conforms to `t`, or is absent. -/
def confO (S : Schema) (t : TypeRef) : Option UVal → Prop
  | none => True
  | some x => conforms S t x

/-- A list view of a side: its items for a list, `none` (the nil `List`) for anything else (an
absent side, `null`; the other kinds are the error branch of `listValue`). -/
def listOfO : Option UVal → Option (List UVal)
  | some (.list vs) => some vs
  | _ => none

/-- A map view of a side, likewise. -/
def mapOfO : Option UVal → Option (List (GoString × UVal))
  | some (.map kvs) => some kvs
  | _ => none

/-- The list branch of `mergeF` with fuel `n` for the items (`mergeF_list`): the items merged in
`mergeKeys` order, absent ones dropped; `none` if none is left. -/
def mergeListOut (n : Nat) (S : Schema) (e : TypeRef) (ks : List GoString)
    (ls rs : List UVal) : Option UVal :=
  let out := (mergeKeys (keysOf ks ls) (keysOf ks rs)).filterMap
    (fun pe => mergeF n S e (itemOf ks ls pe) (itemOf ks rs pe))
  if out.isEmpty then none else some (.list out)

/-- The map branch of `mergeF` with fuel `n` for the entries (`mergeF_map`). -/
def mergeMapOut (n : Nat) (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef)
    (ls rs : List (GoString × UVal)) : Option UVal :=
  let out := (zipLexical (ls.length + rs.length + 1) ls rs).filterMap (fun (k, a, b) =>
    match fieldType fs e k with
    | some t' => (mergeF n S t' a b).map (fun v => (k, v))
    | none => none)
  if out.isEmpty then none else some (.map out)

/-- Fuel enough for the items of two lists (or maps). -/
def fuelL (ls rs : List UVal) : Nat := UVal.sizeL ls + UVal.sizeL rs + 1
def fuelM (ls rs : List (GoString × UVal)) : Nat := UVal.sizeM ls + UVal.sizeM rs + 1

/-- The list branch of `cmpF` with fuel `n` for the items, without the node's own `nodeC`. -/
def cmpListOut (n : Nat) (S : Schema) (e : TypeRef) (ks : List GoString) (p : Path)
    (ls rs : List UVal) : Cmp :=
  let pes := keysOf ks ls ++ (keysOf ks rs).filter (fun x => decide (x ∉ keysOf ks ls))
  Cmp.unionAll (pes.map (fun pe => cmpF n S e (p ++ [pe]) (itemOf ks ls pe) (itemOf ks rs pe)))

/-- The map branch of `cmpF` with fuel `n` for the entries, without the node's `nodeC`. -/
def cmpMapOut (n : Nat) (S : Schema) (fs : List (GoString × TypeRef)) (e : Option TypeRef)
    (p : Path) (ls rs : List (GoString × UVal)) : Cmp :=
  Cmp.unionAll ((zipLexical (ls.length + rs.length + 1) ls rs).map (fun (k, a, b) =>
    match fieldType fs e k with
    | some t' => cmpF n S t' (p ++ [.field k]) a b
    | none => Cmp.none))

/-- Union of two optional sets (the reconcile walker's `toRemove`/`toAdd`, nil or a set):
`finishDescent`'s merge. -/
def optU : Option PathSet → Option PathSet → Option PathSet
  | none, b => b
  | a, none => a
  | some a, some b => some (a.union b)

/-- The reconcile walker's node is itself an atomic node with children: not reached as a member
without children (`b`, `isAtomic`), of an atomic list type, or of an atomic map type with a
non-empty child set `F` (`doList`/`doMap`). -/
def reconTouch (S : Schema) (t : TypeRef) (b : Bool) (F : PathSet) : Bool :=
  !b && match S.find t.name with
    | some (.list _ .atomic _) => true
    | some (.map _ _ .atomic) => !F.isEmpty
    | _ => false

/-- **`reconOut S t p b F`**: what the reconcile walker at the node of path `p`, type `t`,
`isAtomic` `b`, child set `F` (the paths of the field set below the node, relative) adds to
`toRemove` (and `toAdd`): the node itself if it is an atomic node with children, and the atomic
nodes with children below it (`atomicNodes`, shifted by `p`); `none` (nil, nothing set) if
neither. At the root (`p = []`, `b = false`) of an atomic list type the walker sets
`toRemove = NewSet([])`, an empty set (`ins [] = ∅`): `some ∅`. -/
def reconOut (S : Schema) (t : TypeRef) (p : Path) (b : Bool) (F : PathSet) : Option PathSet :=
  let ns := atomicNodes S t F
  if reconTouch S t b F || !ns.isEmpty then
    some ((if reconTouch S t b F then ins p else empty).union (ns.map (p ++ ·)))
  else none

/-- The node is a leaf for the merge and compare walkers (`doLeaf`): a scalar, an atomic list or
map, or a list or map empty (or absent, or `null`) on both sides (`emptyPromoteToLeaf`). -/
def leafAt (S : Schema) (t : TypeRef) (l r : Option UVal) : Bool :=
  match S.find t.name with
  | some (.scalar _) => true
  | some (.list _ rel _) => decide (rel = .atomic) || ((listItems l).isEmpty && (listItems r).isEmpty)
  | some (.map _ _ rel) => decide (rel = .atomic) || ((mapItems l).isEmpty && (mapItems r).isEmpty)
  | none => false

/-- **`cmpBelow S t p l r`**: what the compare walker's `doScalar`/`doList`/`doMap` add at the node
of path `p`: the leaf's change (`leafC`), or the items' or entries' comparisons; `compare` then
adds the node itself (`nodeC`) when it is not a leaf (`cmpO_below`). -/
def cmpBelow (S : Schema) (t : TypeRef) (p : Path) (l r : Option UVal) : Cmp :=
  if leafAt S t l r then leafC p l r else
  match S.find t.name with
  | some (.list e _ ks) => cmpListOut (fuelO l r - 1) S e ks p (listItems l) (listItems r)
  | some (.map fs e _) => cmpMapOut (fuelO l r - 1) S fs e p (mapItems l) (mapItems r)
  | _ => Cmp.none

/-- The atomic nodes with children strictly below a granular node of path `p` (relative child set
`F`), shifted to absolute paths; `none` if there are none (the reconcile walker's `visitListItems`
and `visitMapItems`). -/
def reconBelow (S : Schema) (t : TypeRef) (p : Path) (F : PathSet) : Option PathSet :=
  let ns := atomicNodes S t F
  if ns.isEmpty then none else some (ns.map (p ++ ·))

/-- The key a list item has (`listItemToPathElement` on an associative list with keys `ks`). -/
def itemKeyOk (ks : List GoString) (x : UVal) : Prop := (keyOf ks x).isSome

/-! ## Representation predicates -/

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`isValO v dq o`**: a side of a walker: the nil `Value` (`o = none`), or a wrapper at
fraction `dq` holding `x` (`o = some x`): what a walker method borrows and gives back. -/
def isValO (v : value.Value) (dq : DFrac) : Option UVal → IProp GF
  | none => iprop(⌜v = interface.nil⌝)
  | some x => isValF v dq x

/-- **`isListO l o`**: the nil `value.List` (`o = none`) or a list view of `vs`. -/
def isListO (l : value.List') : Option (List UVal) → IProp GF
  | none => iprop(⌜l = interface.nil⌝)
  | some vs => isListV l vs

/-- **`ownPath s p`**: a walker's path slice `s`, holding `p`, owned with its capacity (a descent
appends to it in place: `prepareDescent`). -/
def ownPath (s : fieldpath.Path) (p : Path) : IProp GF :=
  iprop(isPathF s (DFrac.own 1) p ∗ ownSliceCap fieldpath.PathElement s (DFrac.own 1))

/-- **`spareWalkers V sp`**: the spare walkers of one traversal (`*[]*V`, nil before the first
descent): each owned, its content junk (`prepareDescent` overwrites it whole: `*w2 = *w`). -/
def spareWalkers (V : Type) [TypedPointsto (GF := GF) V] (sp : Loc) : IProp GF :=
  iprop(⌜sp = null⌝ ∨ ∃ (sl : GoSlice) (ws : List Loc), sp ↦ sl ∗ sl ↦* ws ∗
    ownSliceCap Loc sl (DFrac.own 1) ∗ [∗list] w ∈ ws, ∃ v : V, w ↦ v)

/-- **`ownErrs errs es`**: a `ValidationErrors` slice holding `es`, owned with its capacity
(walkers append their children's errors to it and prefix them in place). -/
def ownErrs (errs : GoSlice) (es : List typed.ValidationError) : IProp GF :=
  iprop(errs ↦* es ∗ ownSliceCap typed.ValidationError errs (DFrac.own 1))

/-- **`errsIff errs ok`**: an owned `ValidationErrors` slice, empty exactly when `ok`. -/
def errsIff (errs : GoSlice) (ok : Prop) : IProp GF :=
  iprop(∃ es, ownErrs errs es ∗ ⌜es = [] ↔ ok⌝)

/-- **`noErrs errs`**: an owned, empty `ValidationErrors` slice (nil, or emptied: every walker
on conforming values). -/
def noErrs (errs : GoSlice) : IProp GF := iprop(ownErrs errs [])

/-- **`prefixOk fn`**: a `prefixFn` the walkers' `WithLazyPrefix` may call when there are errors:
nil, or a `func() string` (a path element's `String` method value). -/
def prefixOk (fn : GoFunc) : IProp GF :=
  iprop(⌜fn = func.nil⌝ ∨ {{ True }} (App (Val #fn) (Val #())) {{ (s : GoString), RET #s; True }})

/-- **`atomHandlerOk A a T hv Pre Q`**: the `atomHandler` interface value `(T, hv)` (a walker)
handles the atom `a` of a type holding `A`: the method `handleAtom` dispatches to (`doMap` for a
map, `doScalar` for a scalar, `doList` for a list, with the atom's pointer) takes `Pre` and gives
`Q` of its errors (the interface's bundle, read at the one method called). -/
def atomHandlerOk (A : Atom) (a : schema.Atom) (T : go.GoType) (hv : val) (Pre : IProp GF)
    (Q : GoSlice → IProp GF) : IProp GF :=
  match A with
  | .map _ _ _ => iprop({{ Pre }} (App (Val #(methods T go!"doMap" hv)) (Val #a.Map'))
      {{ (errs : GoSlice), RET #errs; Q errs }})
  | .scalar _ => iprop({{ Pre }} (App (Val #(methods T go!"doScalar" hv)) (Val #a.Scalar'))
      {{ (errs : GoSlice), RET #errs; Q errs }})
  | .list _ _ _ => iprop({{ Pre }} (App (Val #(methods T go!"doList" hv)) (Val #a.List'))
      {{ (errs : GoSlice), RET #errs; Q errs }})

/-- **`isSetO p o`**: a `*fieldpath.Set` that may be nil: `none` nil, else `isSet`. -/
def isSetO (p : Loc) : Option PathSet → IProp GF
  | none => iprop(⌜p = null⌝)
  | some s => isSet p s

/-! ### Typed values and comparisons -/

/-- **`isTVv tv sc S t x`**: a `typed.TypedValue` struct value (a value receiver, a copy) of schema
`sc` holding `S` (in scope), type `t`, value `x` conforming (persistent; `isTV p … ⊣⊢ ∃ tv,
p ↦□ tv ∗ isTVv tv …`: `isTV_isTVv`). -/
def isTVv (tv : typed.TypedValue) (sc : Loc) (S : Schema) (t : TypeRef) (x : UVal) : IProp GF :=
  iprop(⌜tv.schema' = sc⌝ ∗ isVal tv.value' x ∗ isTypeRef tv.typeRef' t ∗ isSchema sc S ∗
    ⌜S.WF ∧ conforms S t x⌝)

/-- **`isTVu tv sc S t x dq`**: a `TypedValue` not validated yet (`AsTyped`'s, before
`Validate`): its value lent at `dq`. -/
def isTVu (tv : typed.TypedValue) (sc : Loc) (S : Schema) (t : TypeRef) (x : UVal) (dq : DFrac) :
    IProp GF :=
  iprop(⌜tv.schema' = sc⌝ ∗ isValF tv.value' dq x ∗ isTypeRef tv.typeRef' t ∗ isSchema sc S ∗
    ⌜S.WF⌝)

/-- **`isComparison c C`**: the `*typed.Comparison` at `c` holds `C` (its three sets; persistent:
neither `Compare`'s caller nor `FilterFields(nil)` writes it; `merge`'s `Updater.update` returns
one). Sealed. -/
@[no_expose] def isComparison (c : Loc) (C : Cmp) : IProp GF :=
  iprop(∃ (r m a : Loc), c ↦□ (typed.Comparison.mk r m a) ∗
    isSet r C.removed ∗ isSet m C.modified ∗ isSet a C.added)

/-- **`ownCmp c C`**: the comparison under construction (the compare walker's): its struct and
its three sets owned (`Set.Insert` updates them in place). -/
def ownCmp (c : Loc) (C : Cmp) : IProp GF :=
  iprop(∃ (r m a : Loc), c ↦ (typed.Comparison.mk r m a) ∗
    ownSet r C.removed ∗ ownSet m C.modified ∗ ownSet a C.added)

/-! ### The merging walker -/

/-- The merging walker's state (`mergingWalker`'s fields the specs follow). -/
structure MWSt where
  lhs : value.Value
  rhs : value.Value
  t : TypeRef
  path : Path
  out : Option UVal
  inLeaf : Bool

/-- **`outRep o mx`**: the merging walker's `out *interface{}`: nil (`none`), or a cell holding
an interface holding `x`, never written again (persistent). -/
def outRep (o : Loc) : Option UVal → IProp GF
  | none => iprop(⌜o = null⌝)
  | some x => iprop(∃ i : GoInterface, o ↦□ i ∗ isIface i x)

/-- **`ruleKeepRHSOk f`**: `f` is `ruleKeepRHS`'s closure: called on a merging walker, it sets
its `out` to its right side, else its left (`leafM`), reading both sides (lent, given back); one
side is present (`merge` checks it first). -/
def ruleKeepRHSOk (f : GoFunc) : IProp GF :=
  iprop(□ ∀ (w : Loc) (v : typed.mergingWalker) (dql dqr : DFrac) (l r : Option UVal),
    {{ w ↦ v ∗ isValO v.lhs' dql l ∗ isValO v.rhs' dqr r ∗ ⌜l.isSome ∨ r.isSome⌝ }}
      (App (Val #f) (Val #w))
    {{ RET #(); ∃ o : Loc, w ↦ { v with out' := o } ∗ outRep o (leafM l r) ∗
        isValO v.lhs' dql l ∗ isValO v.rhs' dqr r }})

/-- **`mwCore w sc S st ps sp a`**: the merging walker's struct at `w` (owned) in state `st`: the
schema `sc` (`isSchema`, in scope), the node's type (`isTypeRef`), path slice `ps`, rule
`ruleKeepRHS`, no post-item hook (`Merge`'s), output `st.out`, spare list `sp`, allocator `a`. -/
def mwCore (w sc : Loc) (S : Schema) (st : MWSt) (ps : fieldpath.Path) (sp : Loc)
    (a : value.Allocator) : IProp GF :=
  iprop(∃ (tr : schema.TypeRef) (rule : GoFunc) (o : Loc),
    w ↦ (typed.mergingWalker.mk st.lhs st.rhs sc tr ps rule func.nil o st.inLeaf sp a) ∗
    isTypeRef tr st.t ∗ isSchema sc S ∗ ⌜S.WF⌝ ∗ ruleKeepRHSOk rule ∗ outRep o st.out)

/-- **`mwOwn w sc S st sp`**: the active merging walker: its struct and the descent's resources
(path buffer, spare walkers at `sp`, allocator). `sp` is explicit: a descent's `finishDescent`
needs the child's spare walkers to be the parent's (Go sets `spareWalkers` only when nil). -/
def mwOwn (w sc : Loc) (S : Schema) (st : MWSt) (sp : Loc) : IProp GF :=
  iprop(∃ (ps : fieldpath.Path) (a : value.Allocator),
    mwCore w sc S st ps sp a ∗ ownPath ps st.path ∗ spareWalkers typed.mergingWalker sp ∗ isAlloc a)

/-- **`mwPooled w`**: a merging walker in `mwPool`: its path emptied (`finishDescent` leaves the
top walker's path at its start, `[]`), no output and not in a leaf (`merge`'s deferred reset;
`merge` does not set them), its spare walkers, its allocator (nil if new: `merge` makes one
then). -/
def mwPooled (w : Loc) : IProp GF :=
  iprop(∃ v : typed.mergingWalker, w ↦ v ∗ ⌜v.out' = null ∧ v.inLeaf' = false⌝ ∗ ownPath v.path' [] ∗
    spareWalkers typed.mergingWalker v.spareWalkers' ∗
    (⌜v.allocator' = interface.nil⌝ ∨ isAlloc v.allocator'))

/-! ### The compare walker -/

/-- The compare walker's state. -/
structure CWSt where
  lhs : value.Value
  rhs : value.Value
  t : TypeRef
  path : Path
  inLeaf : Bool

/-- **`cwCore w sc S st ps c sp a`**: the compare walker's struct (owned), its comparison `c`
(shared by the traversal's walkers: `prepareDescent(pe, tr, w.comparison)`). -/
def cwCore (w sc : Loc) (S : Schema) (st : CWSt) (ps : fieldpath.Path) (c sp : Loc)
    (a : value.Allocator) : IProp GF :=
  iprop(∃ tr : schema.TypeRef,
    w ↦ (typed.compareWalker.mk st.lhs st.rhs sc tr ps c st.inLeaf sp a) ∗
    isTypeRef tr st.t ∗ isSchema sc S ∗ ⌜S.WF⌝)

/-- **`cwOwn w sc S st c C sp`**: the active compare walker, the comparison at `c` holding `C` so
far (owned: the walker inserts into its sets), its spare walkers at `sp` (explicit, as
`mwOwn`'s). -/
def cwOwn (w sc : Loc) (S : Schema) (st : CWSt) (c : Loc) (C : Cmp) (sp : Loc) : IProp GF :=
  iprop(∃ (ps : fieldpath.Path) (a : value.Allocator),
    cwCore w sc S st ps c sp a ∗ ownPath ps st.path ∗ spareWalkers typed.compareWalker sp ∗
    isAlloc a ∗ ownCmp c C)

/-- **`cwPooled w`**: a compare walker in `cmpwPool` (path emptied, not in a leaf, spare walkers,
allocator or nil). -/
def cwPooled (w : Loc) : IProp GF :=
  iprop(∃ v : typed.compareWalker, w ↦ v ∗ ⌜v.inLeaf' = false⌝ ∗ ownPath v.path' [] ∗
    spareWalkers typed.compareWalker v.spareWalkers' ∗
    (⌜v.allocator' = interface.nil⌝ ∨ isAlloc v.allocator'))

/-! ### The field-set walker -/

/-- The field-set walker's state. -/
structure TWSt where
  value : value.Value
  t : TypeRef
  path : Path
  /-- The allocator (Prove phase, 2026-11-19: kept across a method, as `VWSt.alloc`). -/
  alloc : _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.Allocator

/-- **`twCore w sc S st ps s sp a`**: the field-set walker's struct (owned), the set `s` it adds
to (shared by the traversal). -/
def twCore (w sc : Loc) (S : Schema) (st : TWSt) (ps : fieldpath.Path) (s sp : Loc)
    (a : value.Allocator) : IProp GF :=
  iprop(∃ tr : schema.TypeRef,
    w ↦ (typed.toFieldSetWalker.mk st.value sc tr s ps sp a) ∗
    isTypeRef tr st.t ∗ isSchema sc S ∗ ⌜S.WF⌝)

/-- **`twOwn w sc S st s F sp`**: the active field-set walker, the set at `s` holding `F` so far
(owned), its spare walkers at `sp` (explicit, as `mwOwn`'s). -/
def twOwn (w sc : Loc) (S : Schema) (st : TWSt) (s : Loc) (F : PathSet) (sp : Loc) : IProp GF :=
  iprop(∃ ps : fieldpath.Path,
    twCore w sc S st ps s sp st.alloc ∗ ownPath ps st.path ∗ spareWalkers typed.toFieldSetWalker sp ∗
    isAlloc st.alloc ∗ ownSet s F)

/-- **`twPooled w`**: a field-set walker in `tPool` (`finished`: path nil; its spare walkers; its
allocator is replaced at the next `toFieldSetWalker()`). -/
def twPooled (w : Loc) : IProp GF :=
  iprop(∃ v : typed.toFieldSetWalker, w ↦ v ∗ ⌜v.path' = slice.nil⌝ ∗
    spareWalkers typed.toFieldSetWalker v.spareWalkers')

/-! ### The validating walker -/

/-- The validating walker's state. Its allocator `alloc` is part of it (Prove phase, 2026-11-19):
a method's post gives the walker back with the same allocator, which a `defer a.Free(x)`
registered before the call (`doList`, `doMap`, `visitListItems`) and `finishDescent` (the
child's allocator is the parent's) need. -/
structure VWSt where
  value : value.Value
  t : TypeRef
  alloc : _root_.Perennial.sigs_k8s_io.structured_merge_diff.v7.value.Allocator

/-- **`vwCore w sc S st sp a`**: the validating walker's struct (owned), duplicates not allowed
(the scope: no `AllowDuplicates`). -/
def vwCore (w sc : Loc) (S : Schema) (st : VWSt) (sp : Loc) (a : value.Allocator) : IProp GF :=
  iprop(∃ tr : schema.TypeRef,
    w ↦ (typed.validatingObjectWalker.mk st.value sc tr false sp a) ∗
    isTypeRef tr st.t ∗ isSchema sc S ∗ ⌜S.WF⌝)

/-- **`vwOwn w sc S st sp`**: the active validating walker, its spare walkers at `sp` (explicit,
as `mwOwn`'s). -/
def vwOwn (w sc : Loc) (S : Schema) (st : VWSt) (sp : Loc) : IProp GF :=
  iprop(vwCore w sc S st sp st.alloc ∗ spareWalkers typed.validatingObjectWalker sp ∗ isAlloc st.alloc)

/-- **`vwPooled w`**: a validating walker in `vPool` (spare walkers; allocator or nil). -/
def vwPooled (w : Loc) : IProp GF :=
  iprop(∃ v : typed.validatingObjectWalker, w ↦ v ∗
    spareWalkers typed.validatingObjectWalker v.spareWalkers' ∗
    (⌜v.allocator' = interface.nil⌝ ∨ isAlloc v.allocator'))

/-! ### The reconcile walker -/

/-- The reconcile walker's state: the node's type, path, and whether it was reached as a member
of the field set without children (`isAtomic`). -/
structure RWSt where
  t : TypeRef
  path : Path
  isAtomic : Bool

/-- **`rwCore w sc S st ps fs tv rem add sp`**: the reconcile walker's struct (owned): its node's
child set `fs` (nil for a member without children), the live object `tv` (copied, never read),
its accumulators `toRemove`/`toAdd` (`rem`, `add`: nil or a set). -/
def rwCore (w sc : Loc) (S : Schema) (st : RWSt) (ps : fieldpath.Path) (fs tv rem add sp : Loc) :
    IProp GF :=
  iprop(∃ tr : schema.TypeRef,
    w ↦ (typed.reconcileWithSchemaWalker.mk tv sc fs tr ps st.isAtomic rem add sp) ∗
    isTypeRef tr st.t ∗ isSchema sc S ∗ ⌜S.WF⌝)

/-- **`rwOwn w sc S st F R A sp`**: the active reconcile walker, its node's child set `F`
(`none`: nil), its accumulators holding `R` and `A` (`none`: nil), its spare walkers at `sp`
(explicit, as `mwOwn`'s). -/
def rwOwn (w sc : Loc) (S : Schema) (st : RWSt) (F R A : Option PathSet) (sp : Loc) : IProp GF :=
  iprop(∃ (ps : fieldpath.Path) (fs tv rem add : Loc),
    rwCore w sc S st ps fs tv rem add sp ∗ ownPath ps st.path ∗ isSetO fs F ∗ isSetO rem R ∗
    isSetO add A ∗ spareWalkers typed.reconcileWithSchemaWalker sp)

/-- **`rwPooled w`**: a reconcile walker in `fmPool` (`finished`: path nil, accumulators nil;
`isAtomic` false: only a child's is ever set; its spare walkers). -/
def rwPooled (w : Loc) : IProp GF :=
  iprop(∃ v : typed.reconcileWithSchemaWalker, w ↦ v ∗
    ⌜v.path' = slice.nil ∧ v.isAtomic' = false ∧ v.toRemove' = null ∧ v.toAdd' = null⌝ ∗
    spareWalkers typed.reconcileWithSchemaWalker v.spareWalkers')

/-! ### The removing walker -/

/-- **`rmOwn w sc S x R a out`**: a removing walker (`removeItemsWithSchema`'s, not pooled, no
descent: each item or entry is removed from by a fresh call) over the value `v`, removing the set
at `rp` holding `R`, not extracting (`shouldExtract` false: `RemoveItems`), its output interface
`out`. -/
def rmOwn (w sc : Loc) (S : Schema) (v : value.Value) (rp : Loc) (R : PathSet)
    (a : value.Allocator) (out : GoInterface) : IProp GF :=
  iprop(w ↦ (typed.removingWalker.mk v out sc rp a false) ∗ isSchema sc S ∗ ⌜S.WF⌝ ∗
    isSet rp R ∗ isAlloc a)

/-! ### The package fact -/

/-- A pool's predicate for walkers of struct type `T`: an interface holding a `*T` with `P`. -/
def pooledAs (T : go.GoType) (P : Loc → IProp GF) (x : GoAny) : IProp GF :=
  iprop(∃ w : Loc, ⌜x = interface.mkOk (go.GoType.PointerType T) #w⌝ ∗ P w)

/-- **`typedPools`**: the `typed` package's fact (what `isPkgInit typed` must give,
`typedPkgInit_pools.law`): `ruleKeepRHS` holds its closure, and each walker pool holds walkers
with their pooled invariant (`New` makes a zero walker, which has it). -/
def typedPools : IProp GF :=
  iprop((∃ f : GoFunc, (globalAddr typed.ruleKeepRHS) ↦□ f ∗ ruleKeepRHSOk f) ∗
    (∃ f : GoFunc, sync.isPool (globalAddr typed.mwPool) f iprop(True)
      (pooledAs typed.mergingWalker.ty mwPooled)) ∗
    (∃ f : GoFunc, sync.isPool (globalAddr typed.cmpwPool) f iprop(True)
      (pooledAs typed.compareWalker.ty cwPooled)) ∗
    (∃ f : GoFunc, sync.isPool (globalAddr typed.tPool) f iprop(True)
      (pooledAs typed.toFieldSetWalker.ty twPooled)) ∗
    (∃ f : GoFunc, sync.isPool (globalAddr typed.vPool) f iprop(True)
      (pooledAs typed.validatingObjectWalker.ty vwPooled)) ∗
    (∃ f : GoFunc, sync.isPool (globalAddr typed.fmPool) f iprop(True)
      (pooledAs typed.reconcileWithSchemaWalker.ty rwPooled)))

end own

end smd
end EtcdGrove
end Perennial
