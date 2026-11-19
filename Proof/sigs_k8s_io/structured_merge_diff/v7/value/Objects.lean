/-
**The `value` package's objects and interfaces** (structured-merge-diff v7.0.0): the vocabulary
of the per-function specs of `value` beyond `Defs.lean` (`notes/smd-plan.md`, "The call DAG",
the `value` rows). Draft (2026-11-19): definitions and laws stated, nothing proved.

What a client of `value` holds, besides a value (`isValF`, `Defs.lean`):

- **a map view** `isMapV m kvs`: a `value.Map` from `Value.AsMap`/`AsMapUsing` (a
  `mapUnstructuredString` over the value's `map[string]interface{}`), persistent; `isMapO m o`
  admits the nil `Map` too (`o = none`), as `MapZipUsing` and the walkers' `derefMap` pass it;
- **a list view** `isListV l vs`: a `value.List` from `AsList`/`AsListUsing` (a
  `listUnstructured`), or a pointer to one (`listUnstructured.EqualsUsing` passes `&l` to
  `ListEqualsUsing`), persistent;
- **an allocator** `isAlloc a`: `HeapAllocator` (any `*heapAllocator`: its methods never read
  the receiver) or one from `NewFreelistAllocator`, whose freelists it owns, so **exclusive**:
  the walkers thread one allocator through a whole traversal, and every `value` function that
  takes one gives it back;
- **a freeable object** `freeable x`: what `Allocator.Free(x)` consumes. A wrapper must be owned
  **whole** (`isValF v (DFrac.own 1) x ⊢ freeable v`, `isValF_freeable`): the freelist allocator
  clears it and hands it out again, so a client can free only a wrapper no one else holds a
  share of (round 1's vocabulary finding F1). A `Map`, a `List` and an `*emptyRange` are freed as
  no-ops (`freeable` is `True` of them: `Free`'s type switch has no case), the reflection objects
  are out of scope (`False`);
- **a list range** `ownRange r vs i` (internal to `value`: only `ListEqualsUsing`/
  `ListCompareUsing` iterate): the range's cursor at `i` over `vs`; `Item` lends its wrapper.

**Callbacks** (`Map.Iterate`/`IterateUsing`, `MapZipUsing` and the zips): one spec each,
parametric in the callback's contract (`examples/apply-uber-contract.md`): a client invariant
`I done` over the keys already visited, and a stop predicate `Q` for a callback returning
`false`. A callback is lent each value's wrapper **whole** (`isValF v (DFrac.own 1) x`) and gives
it back: the implementation rewrites it for the next key (`reuse`) or frees it.
`iterOk`/`zipOk` state where in the iteration a call happens (any order for a Go map's
`range` and for `Unordered`; the sorted union of the keys for `LexicalKeyOrder`).

**Interface bundles** (PRINCIPLES, "Canonical specs are per (concrete type, method); an interface
value gets a bundle"): every concrete method has its spec file
(`Spec/.../value/<T>__<M>.lean`); a client holding a `value.Value`, `Map`, `List`, `ListRange` or
`Allocator` interface value uses the bundle of its method triples (`valueIfaceM`, `mapIfaceM`, `listIfaceM`,
`rangeIfaceM`, `allocIfaceM`: persistent, as Perennial's `sync.isLocker`), obtained from the representation
predicate by the laws `isValF_methods`, `isMapV_methods`, `isListV_methods`, `ownRange_methods`,
`isAlloc_methods` (`Laws` below), each proved (later, in the linking tier) from the concrete
specs. Each triple of a bundle is the concrete spec read at the interface's dynamic receiver, so
the laws are instances.

Lean-first (2026-11-19, notes/smd-plan.md).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

/-! ## Pure helpers -/

/-- `Value.IsMap` and its siblings on a value of the scope (no floats). -/
def UVal.isMapB : UVal → Bool | .map _ => true | _ => false
def UVal.isListB : UVal → Bool | .list _ => true | _ => false
def UVal.isBoolB : UVal → Bool | .bool _ => true | _ => false
def UVal.isIntB : UVal → Bool | .int _ => true | _ => false
def UVal.isStrB : UVal → Bool | .str _ => true | _ => false
def UVal.isNullB : UVal → Bool | .null => true | _ => false

/-- The keys of an association list, in its order. -/
def kvKeys {α : Type} (kvs : List (GoString × α)) : List GoString := kvs.map (·.1)

/-- The entries of a map that may be nil (`none`: the nil `Map`, read as empty). -/
def kvsOrEmpty (o : Option (List (GoString × UVal))) : List (GoString × UVal) := o.getD []

/-- The keys a zip of two maps visits, sorted (the union of their keys; `MapZip` in
`LexicalKeyOrder` visits them in this order). -/
def zipKeys (ol or_ : Option (List (GoString × UVal))) : List GoString :=
  let l := kvsOrEmpty ol
  let r := kvsOrEmpty or_
  (zipLexical (l.length + r.length + 1) l r).map (·.1)

/-- **Where an iteration's step happens**: the callback is called on key `k` after the keys
`done`; `keys` are all the keys the iteration visits. In order (`ordered`): `done ++ [k]` is a
prefix of `keys`; in any order: `k` is a key not yet visited. -/
def mapIterStep (ordered : Bool) (keys done : List GoString) (k : GoString) : Prop :=
  if ordered then (done ++ [k]).IsPrefix keys else k ∈ keys ∧ k ∉ done

/-- An iteration that ran to the end visited `keys`: in order, exactly; in any order, a
permutation of them. -/
def mapIterDone (ordered : Bool) (keys done : List GoString) : Prop :=
  if ordered then done = keys else done.Perm keys

/-- `MapTraverseOrder`: `Unordered` (0) or `LexicalKeyOrder` (1); any other value panics. -/
def zipOrderOk (order : w64) : Prop := order = W64 0 ∨ order = W64 1

/-! ## Representation predicates -/

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The separating conjunction of `f` over a list (internal). -/
def valueSepL {α : Type} (f : α → IProp GF) (xs : List α) : IProp GF :=
  xs.foldr (fun a acc => iprop(f a ∗ acc)) iprop(True)

/-- **`isMapV m kvs`**: the `value.Map` `m` is the `mapUnstructuredString` view of a
`map[string]interface{}` holding the canonical entries `kvs` (persistent). Sealed. -/
@[no_expose] def isMapV (m : value.Map) (kvs : List (GoString × UVal)) : IProp GF :=
  iprop(∃ gm : GoMap, ⌜m = interface.mkOk value.mapUnstructuredString.ty #gm⌝ ∗
    isIface (interface.mkOk mapStrIfaceTy #gm) (.map kvs))

/-- **`isMapO m o`**: `m` is the nil `Map` (`o = none`) or `isMapV m kvs` (`o = some kvs`). -/
def isMapO (m : value.Map) : Option (List (GoString × UVal)) → IProp GF
  | none => iprop(⌜m = interface.nil⌝)
  | some kvs => isMapV m kvs

/-- **`isListV l vs`**: the `value.List` `l` is a `listUnstructured` over a `[]interface{}`
holding `vs`, or a pointer to one (persistent). Sealed. -/
@[no_expose] def isListV (l : value.List') (vs : List UVal) : IProp GF :=
  iprop(∃ sl : GoSlice, isIface (interface.mkOk sliceIfaceTy #sl) (.list vs) ∗
    (⌜l = interface.mkOk value.listUnstructured.ty #sl⌝ ∨
     ∃ p : Loc, ⌜l = interface.mkOk (go.GoType.PointerType value.listUnstructured.ty) #p⌝ ∗
       p ↦□ sl))

/-- A wrapper owned whole, its content arbitrary (internal: what an allocator hands out and
`Free` takes back). -/
@[no_expose] def wrapperOwn (q : Loc) : IProp GF :=
  iprop(∃ i : GoInterface, q ↦ value.valueUnstructured.mk i)

/-- A `*listUnstructuredRange` owned whole, with its wrapper (internal). -/
@[no_expose] def rangeOwn (q : Loc) : IProp GF :=
  iprop(∃ r : value.listUnstructuredRange, q ↦ r ∗ wrapperOwn r.vv')

/-- A `freelist[*T]` owned whole: its spare objects, each `own`, and its `new` closure making a
fresh one (internal). -/
@[no_expose] def freelistOwn (fp : Loc) (own : Loc → IProp GF) : IProp GF :=
  iprop(∃ fl : value.freelist Loc, fp ↦ fl ∗
    (∃ qs : List Loc, fl.list' ↦* qs ∗ ownSliceCap Loc fl.list' (DFrac.own 1) ∗ valueSepL own qs) ∗
    {{ True }} (App (Val #fl.new') (Val #())) {{ (q : Loc), RET #q; own q }})

/-- **`isAlloc a`**: `a` is a usable `value.Allocator`: a `*heapAllocator`, or a
`*freelistAllocator` (`NewFreelistAllocator`) whose two unstructured freelists it owns
(exclusive). Sealed. -/
@[no_expose] def isAlloc (a : value.Allocator) : IProp GF :=
  iprop((∃ p : Loc, ⌜a = interface.mkOk (go.GoType.PointerType value.heapAllocator.ty) #p⌝) ∨
    (∃ (p : Loc) (fa : value.freelistAllocator),
      ⌜a = interface.mkOk (go.GoType.PointerType value.freelistAllocator.ty) #p⌝ ∗ p ↦□ fa ∗
      freelistOwn fa.valueUnstructured' wrapperOwn ∗
      freelistOwn fa.listUnstructuredRange' rangeOwn))

open Classical in
/-- **`freeable x`**: what `Allocator.Free(x)` consumes: a wrapper or a list range owned whole;
nothing for an object `Free` ignores (`Map`, `List`, `*emptyRange`, nil); the reflection objects
are out of scope (`False`). Sealed. -/
@[no_expose] def freeable (x : GoInterface) : IProp GF :=
  match x with
  | .nil => iprop(True)
  | .ok ⟨ty, v⟩ =>
    if ty = go.GoType.PointerType value.valueUnstructured.ty then
      iprop(∃ q : Loc, ⌜v = #q⌝ ∗ wrapperOwn q)
    else if ty = go.GoType.PointerType value.listUnstructuredRange.ty then
      iprop(∃ q : Loc, ⌜v = #q⌝ ∗ rangeOwn q)
    else if ty = go.GoType.PointerType value.valueReflect.ty ∨
        ty = go.GoType.PointerType value.mapReflect.ty ∨
        ty = go.GoType.PointerType value.structReflect.ty ∨
        ty = go.GoType.PointerType value.listReflect.ty ∨
        ty = go.GoType.PointerType value.listReflectRange.ty then iprop(False)
    else iprop(True)

/-- **`ownRange r vs i`**: the `value.ListRange` `r` iterates over `vs`, its cursor at `i` (`-1`
before the first `Next`): `EmptyRange` for an empty list (its cursor at least `-1`: its `Next`
returns `false` whatever the cursor, which is `n + 1 < 0` only from `-1` on; Prove phase,
2026-11-19), else a `*listUnstructuredRange` owned with its wrapper (internal to `value`). -/
@[no_expose] def ownRange (r : value.ListRange) (vs : List UVal) (i : Int) : IProp GF :=
  iprop((∃ q : Loc, ⌜r = interface.mkOk (go.GoType.PointerType value.emptyRange.ty) #q ∧ vs = [] ∧ -1 ≤ i⌝) ∨
    (∃ (q : Loc) (sl : GoSlice) (w : Loc) (iw : w64),
      ⌜r = interface.mkOk (go.GoType.PointerType value.listUnstructuredRange.ty) #q ∧
        iw.toInt = i⌝ ∗
      q ↦ value.listUnstructuredRange.mk sl w iw ∗
      isIface (interface.mkOk sliceIfaceTy #sl) (.list vs) ∗ wrapperOwn w))

/-- A callback's argument for one side of a zip: the nil `Value` for a key the side lacks, else
a wrapper lent whole. -/
def optValF (v : value.Value) : Option UVal → IProp GF
  | none => iprop(⌜v = interface.nil⌝)
  | some x => isValF v (DFrac.own 1) x

/-! ## Callback contracts -/

/-- **`iterFnOk fn kvs I Q`**: the contract of a `Map.Iterate` callback over the entries `kvs`
(heap allocator: no allocator to thread): called on a key `k` not yet visited (after `done`),
with its value's wrapper lent whole; it gives the wrapper back, and returns `true` with the
invariant advanced, or `false` with `Q` (the iteration stops). Persistent. -/
def iterFnOk (fn : GoFunc) (kvs : List (GoString × UVal))
    (I : List GoString → IProp GF) (Q : IProp GF) : IProp GF :=
  iprop(□ ∀ (done : List GoString) (k : GoString) (x : UVal) (v : value.Value),
    ⌜lookupKV k kvs = some x ∧ mapIterStep false (kvKeys kvs) done k⌝ -∗
    {{ I done ∗ isValF v (DFrac.own 1) x }}
      (App (App (Val #fn) (Val #k)) (Val #v))
    {{ (b : Bool), RET #b; isValF v (DFrac.own 1) x ∗
        (if b then I (done ++ [k]) else Q) }})

/-- **`iterUFnOk a fn kvs I Q`**: as `iterFnOk`, for `IterateUsing(a, fn)`: the callback also
gets the allocator `a` (`isAlloc a`) and gives it back. -/
def iterUFnOk (a : value.Allocator) (fn : GoFunc) (kvs : List (GoString × UVal))
    (I : List GoString → IProp GF) (Q : IProp GF) : IProp GF :=
  iprop(□ ∀ (done : List GoString) (k : GoString) (x : UVal) (v : value.Value),
    ⌜lookupKV k kvs = some x ∧ mapIterStep false (kvKeys kvs) done k⌝ -∗
    {{ isAlloc a ∗ I done ∗ isValF v (DFrac.own 1) x }}
      (App (App (Val #fn) (Val #k)) (Val #v))
    {{ (b : Bool), RET #b; isAlloc a ∗ isValF v (DFrac.own 1) x ∗
        (if b then I (done ++ [k]) else Q) }})

/-- **`zipFnOk a ordered fn ol or_ I Q`**: the contract of a `MapZip` callback over the maps
`ol`, `or_` (`none`: nil): called on each key of the union once (in sorted order if `ordered`),
with each side's value (`optValF`: nil where the side lacks the key, else its wrapper lent
whole) and the allocator; it gives them back, and returns `true` with the invariant advanced or
`false` with `Q`. Persistent. -/
def zipFnOk (a : value.Allocator) (ordered : Bool) (fn : GoFunc)
    (ol or_ : Option (List (GoString × UVal)))
    (I : List GoString → IProp GF) (Q : IProp GF) : IProp GF :=
  iprop(□ ∀ (done : List GoString) (k : GoString) (vl vr : value.Value),
    ⌜mapIterStep ordered (zipKeys ol or_) done k⌝ -∗
    {{ isAlloc a ∗ I done ∗ optValF vl (lookupKV k (kvsOrEmpty ol)) ∗
        optValF vr (lookupKV k (kvsOrEmpty or_)) }}
      (App (App (App (Val #fn) (Val #k)) (Val #vl)) (Val #vr))
    {{ (b : Bool), RET #b; isAlloc a ∗ optValF vl (lookupKV k (kvsOrEmpty ol)) ∗
        optValF vr (lookupKV k (kvsOrEmpty or_)) ∗ (if b then I (done ++ [k]) else Q) }})

/-- The post of an iteration over `keys`: it ran to the end (`true`, every key visited) or a
callback stopped it (`false`, `Q`). -/
def mapIterPost (ordered : Bool) (keys : List GoString) (I : List GoString → IProp GF)
    (Q : IProp GF) (r : Bool) : IProp GF :=
  if r then iprop(∃ done, ⌜mapIterDone ordered keys done⌝ ∗ I done) else Q

/-! ## Interface bundles -/

/-- **`valueIfaceM i`**: the `value.Value` interface's method triples at the receiver `i`, over
`isValF (.ok i) dq x` (any share, given back). Persistent. -/
def valueIfaceM (i : GoInterfaceOk) : IProp GF :=
  iprop(
    (∀ dq x, {{ isValF (.ok i) dq x }} (App (Val #(methods i.ty go!"IsMap" i.v)) (Val #()))
      {{ (r : Bool), RET #r; isValF (.ok i) dq x ∗ ⌜r = x.isMapB⌝ }}) ∗
    (∀ dq x, {{ isValF (.ok i) dq x }} (App (Val #(methods i.ty go!"IsList" i.v)) (Val #()))
      {{ (r : Bool), RET #r; isValF (.ok i) dq x ∗ ⌜r = x.isListB⌝ }}) ∗
    (∀ dq x, {{ isValF (.ok i) dq x }} (App (Val #(methods i.ty go!"IsBool" i.v)) (Val #()))
      {{ (r : Bool), RET #r; isValF (.ok i) dq x ∗ ⌜r = x.isBoolB⌝ }}) ∗
    (∀ dq x, {{ isValF (.ok i) dq x }} (App (Val #(methods i.ty go!"IsInt" i.v)) (Val #()))
      {{ (r : Bool), RET #r; isValF (.ok i) dq x ∗ ⌜r = x.isIntB⌝ }}) ∗
    (∀ dq x, {{ isValF (.ok i) dq x }} (App (Val #(methods i.ty go!"IsFloat" i.v)) (Val #()))
      {{ (r : Bool), RET #r; isValF (.ok i) dq x ∗ ⌜r = false⌝ }}) ∗
    (∀ dq x, {{ isValF (.ok i) dq x }} (App (Val #(methods i.ty go!"IsString" i.v)) (Val #()))
      {{ (r : Bool), RET #r; isValF (.ok i) dq x ∗ ⌜r = x.isStrB⌝ }}) ∗
    (∀ dq x, {{ isValF (.ok i) dq x }} (App (Val #(methods i.ty go!"IsNull" i.v)) (Val #()))
      {{ (r : Bool), RET #r; isValF (.ok i) dq x ∗ ⌜r = x.isNullB⌝ }}) ∗
    (∀ dq kvs, {{ isValF (.ok i) dq (.map kvs) }} (App (Val #(methods i.ty go!"AsMap" i.v)) (Val #()))
      {{ (m : value.Map), RET #m; isValF (.ok i) dq (.map kvs) ∗ isMapV m kvs }}) ∗
    (∀ dq kvs (a : value.Allocator), {{ isValF (.ok i) dq (.map kvs) }}
      (App (Val #(methods i.ty go!"AsMapUsing" i.v)) (Val #a))
      {{ (m : value.Map), RET #m; isValF (.ok i) dq (.map kvs) ∗ isMapV m kvs }}) ∗
    (∀ dq vs, {{ isValF (.ok i) dq (.list vs) }} (App (Val #(methods i.ty go!"AsList" i.v)) (Val #()))
      {{ (l : value.List'), RET #l; isValF (.ok i) dq (.list vs) ∗ isListV l vs }}) ∗
    (∀ dq vs (a : value.Allocator), {{ isValF (.ok i) dq (.list vs) }}
      (App (Val #(methods i.ty go!"AsListUsing" i.v)) (Val #a))
      {{ (l : value.List'), RET #l; isValF (.ok i) dq (.list vs) ∗ isListV l vs }}) ∗
    (∀ dq b, {{ isValF (.ok i) dq (.bool b) }} (App (Val #(methods i.ty go!"AsBool" i.v)) (Val #()))
      {{ (r : Bool), RET #r; isValF (.ok i) dq (.bool b) ∗ ⌜r = b⌝ }}) ∗
    (∀ dq n, {{ isValF (.ok i) dq (.int n) }} (App (Val #(methods i.ty go!"AsInt" i.v)) (Val #()))
      {{ (r : w64), RET #r; isValF (.ok i) dq (.int n) ∗ ⌜r = n⌝ }}) ∗
    (∀ dq s, {{ isValF (.ok i) dq (.str s) }} (App (Val #(methods i.ty go!"AsString" i.v)) (Val #()))
      {{ (r : GoString), RET #r; isValF (.ok i) dq (.str s) ∗ ⌜r = s⌝ }}) ∗
    (∀ dq x, {{ isValF (.ok i) dq x }} (App (Val #(methods i.ty go!"Unstructured" i.v)) (Val #()))
      {{ (u : GoInterface), RET #u; isValF (.ok i) dq x ∗ isIface u x }}))

/-- **`allocIfaceM i`**: the `value.Allocator` interface's method triples at `i`, over
`isAlloc (.ok i)`. Persistent. -/
def allocIfaceM (i : GoInterfaceOk) : IProp GF :=
  iprop(
    (∀ x : GoInterface, {{ isAlloc (.ok i) ∗ freeable x }}
      (App (Val #(methods i.ty go!"Free" i.v)) (Val #x))
      {{ RET #(); isAlloc (.ok i) }}) ∗
    ({{ isAlloc (.ok i) }} (App (Val #(methods i.ty go!"allocValueUnstructured" i.v)) (Val #()))
      {{ (q : Loc), RET #q; isAlloc (.ok i) ∗ wrapperOwn q }}) ∗
    ({{ isAlloc (.ok i) }} (App (Val #(methods i.ty go!"allocListUnstructuredRange" i.v)) (Val #()))
      {{ (q : Loc), RET #q; isAlloc (.ok i) ∗ rangeOwn q }}))

/-- **`mapIfaceM i`**: the `value.Map` interface's method triples at `i` (the ones SMD calls), over
`isMapV (.ok i) kvs`. Persistent. -/
def mapIfaceM (i : GoInterfaceOk) : IProp GF :=
  iprop(
    (∀ kvs, {{ isMapV (.ok i) kvs }} (App (Val #(methods i.ty go!"Length" i.v)) (Val #()))
      {{ (r : w64), RET #r; ⌜r.toInt = kvs.length⌝ }}) ∗
    (∀ kvs, {{ isMapV (.ok i) kvs }} (App (Val #(methods i.ty go!"Empty" i.v)) (Val #()))
      {{ (r : Bool), RET #r; ⌜r = true ↔ kvs = []⌝ }}) ∗
    (∀ kvs (k : GoString), {{ isMapV (.ok i) kvs }} (App (Val #(methods i.ty go!"Has" i.v)) (Val #k))
      {{ (r : Bool), RET #r; ⌜r = (lookupKV k kvs).isSome⌝ }}) ∗
    (∀ kvs (k : GoString), {{ isMapV (.ok i) kvs }} (App (Val #(methods i.ty go!"Get" i.v)) (Val #k))
      {{ (v : value.Value) (ok : Bool), RET (PairV #v #ok);
          ⌜ok = (lookupKV k kvs).isSome⌝ ∗ optValF v (lookupKV k kvs) }}) ∗
    (∀ kvs (a : value.Allocator) (k : GoString), {{ isMapV (.ok i) kvs ∗ isAlloc a }}
      (App (App (Val #(methods i.ty go!"GetUsing" i.v)) (Val #a)) (Val #k))
      {{ (v : value.Value) (ok : Bool), RET (PairV #v #ok); isAlloc a ∗
          ⌜ok = (lookupKV k kvs).isSome⌝ ∗ optValF v (lookupKV k kvs) }}) ∗
    (∀ kvs (fn : GoFunc) (I : List GoString → IProp GF) (Q : IProp GF),
      {{ isMapV (.ok i) kvs ∗ iterFnOk fn kvs I Q ∗ I [] }}
      (App (Val #(methods i.ty go!"Iterate" i.v)) (Val #fn))
      {{ (r : Bool), RET #r; mapIterPost false (kvKeys kvs) I Q r }}) ∗
    (∀ kvs (a : value.Allocator) (fn : GoFunc) (I : List GoString → IProp GF) (Q : IProp GF),
      {{ isMapV (.ok i) kvs ∗ isAlloc a ∗ iterUFnOk a fn kvs I Q ∗ I [] }}
      (App (App (Val #(methods i.ty go!"IterateUsing" i.v)) (Val #a)) (Val #fn))
      {{ (r : Bool), RET #r; isAlloc a ∗ mapIterPost false (kvKeys kvs) I Q r }}) ∗
    (∀ kvs kvs' (a : value.Allocator) (o : value.Map),
      {{ isMapV (.ok i) kvs ∗ isMapV o kvs' ∗ isAlloc a }}
      (App (App (Val #(methods i.ty go!"EqualsUsing" i.v)) (Val #a)) (Val #o))
      {{ (r : Bool), RET #r; isAlloc a ∗ ⌜r = true ↔ kvs = kvs'⌝ }}) ∗
    (∀ kvs or_ (a : value.Allocator) (o : value.Map) (order : w64) (fn : GoFunc)
        (I : List GoString → IProp GF) (Q : IProp GF),
      {{ isMapV (.ok i) kvs ∗ isMapO o or_ ∗ isAlloc a ∗ ⌜zipOrderOk order⌝ ∗
          zipFnOk a (order = W64 1) fn (some kvs) or_ I Q ∗ I [] }}
      (App (App (App (App (Val #(methods i.ty go!"ZipUsing" i.v)) (Val #a)) (Val #o)) (Val #order)) (Val #fn))
      {{ (r : Bool), RET #r; isAlloc a ∗
          mapIterPost (order = W64 1) (zipKeys (some kvs) or_) I Q r }}))

/-- **`listIfaceM i`**: the `value.List` interface's method triples at `i` (the ones SMD calls), over
`isListV (.ok i) vs`. Persistent. -/
def listIfaceM (i : GoInterfaceOk) : IProp GF :=
  iprop(
    (∀ vs, {{ isListV (.ok i) vs }} (App (Val #(methods i.ty go!"Length" i.v)) (Val #()))
      {{ (r : w64), RET #r; ⌜r.toInt = vs.length⌝ }}) ∗
    (∀ vs (n : w64) x, {{ isListV (.ok i) vs ∗ ⌜0 ≤ n.toInt ∧ vs[n.toInt.toNat]? = some x⌝ }}
      (App (Val #(methods i.ty go!"At" i.v)) (Val #n))
      {{ (v : value.Value), RET #v; isValF v (DFrac.own 1) x }}) ∗
    (∀ vs (a : value.Allocator) (n : w64) x,
      {{ isListV (.ok i) vs ∗ isAlloc a ∗ ⌜0 ≤ n.toInt ∧ vs[n.toInt.toNat]? = some x⌝ }}
      (App (App (Val #(methods i.ty go!"AtUsing" i.v)) (Val #a)) (Val #n))
      {{ (v : value.Value), RET #v; isAlloc a ∗ isValF v (DFrac.own 1) x }}) ∗
    (∀ vs (a : value.Allocator), {{ isListV (.ok i) vs ∗ isAlloc a }}
      (App (Val #(methods i.ty go!"RangeUsing" i.v)) (Val #a))
      {{ (r : value.ListRange), RET #r; isAlloc a ∗ ownRange r vs (-1) }}) ∗
    (∀ vs ws (a : value.Allocator) (o : value.List'),
      {{ isListV (.ok i) vs ∗ isListV o ws ∗ isAlloc a }}
      (App (App (Val #(methods i.ty go!"EqualsUsing" i.v)) (Val #a)) (Val #o))
      {{ (r : Bool), RET #r; isAlloc a ∗ ⌜r = true ↔ vs = ws⌝ }}))

/-- **`rangeIfaceM i`**: the `value.ListRange` interface's method triples at `i`, over
`ownRange (.ok i) vs n` (internal to `value`). `Item` lends the range's wrapper; giving it back
gives the range back. Persistent. -/
def rangeIfaceM (i : GoInterfaceOk) : IProp GF :=
  iprop(
    (∀ vs (n : Int), {{ ownRange (.ok i) vs n }} (App (Val #(methods i.ty go!"Next" i.v)) (Val #()))
      {{ (b : Bool), RET #b; ownRange (.ok i) vs (n + 1) ∗ ⌜b = decide (n + 1 < vs.length)⌝ }}) ∗
    (∀ vs (n : Int) x, {{ ownRange (.ok i) vs n ∗ ⌜0 ≤ n ∧ vs[n.toNat]? = some x⌝ }}
      (App (Val #(methods i.ty go!"Item" i.v)) (Val #()))
      {{ (j : w64) (v : value.Value), RET (PairV #j #v); ⌜j.toInt = n⌝ ∗
          isValF v (DFrac.own 1) x ∗ (isValF v (DFrac.own 1) x -∗ ownRange (.ok i) vs n) }}))

end own

/-! ## Laws (stated; proved after the freeze: the next phase's invariant work) -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The views are persistent. -/
def isMapV_persistent.law : Prop := ∀ m kvs, isMapV (GF := GF) m kvs ⊢ □ isMapV m kvs
def isListV_persistent.law : Prop := ∀ l vs, isListV (GF := GF) l vs ⊢ □ isListV l vs

/-- A wrapper owned whole can be freed (F1: only the whole wrapper). -/
def isValF_freeable.law : Prop :=
  ∀ v x, isValF (GF := GF) v (DFrac.own 1) x ⊢ freeable v

/-- `Free` of a view or the nil interface takes nothing. -/
def freeable_view.law : Prop :=
  (∀ m kvs, isMapV (GF := GF) m kvs ⊢ isMapV m kvs ∗ freeable m) ∧
  (∀ l vs, isListV (GF := GF) l vs ⊢ isListV l vs ∗ freeable l) ∧
  (⊢ freeable (GF := GF) interface.nil)

/-- A range, finished, can be freed. -/
def ownRange_freeable.law : Prop := ∀ r vs n, ownRange (GF := GF) r vs n ⊢ freeable r

/-- Agreement of the views. -/
def isMapV_agree.law : Prop :=
  ∀ m a b, isMapV (GF := GF) m a ∗ isMapV m b ⊢ ⌜a = b⌝
def isListV_agree.law : Prop :=
  ∀ l a b, isListV (GF := GF) l a ∗ isListV l b ⊢ ⌜a = b⌝

/-- Map views are canonical (the entries of a `UVal` map are). -/
def isMapV_sorted.law : Prop :=
  ∀ m kvs, isMapV (GF := GF) m kvs ⊢ ⌜keysSorted kvs = true⌝

/-- **The bundles** (dispatch laws), each proved from the concrete `<T>.<M>` (and `_ptr`) specs
of the interface's dynamic types in scope (`isPkgInit value`: `HeapAllocator`, `EmptyRange`). -/
def isValF_methods.law : Prop :=
  ∀ v dq x, isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isValF v dq x ⊢
    isValF v dq x ∗ ∃ i, ⌜v = .ok i⌝ ∗ □ valueIfaceM i
def isAlloc_methods.law : Prop :=
  ∀ a, isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isAlloc a ⊢ isAlloc a ∗ ∃ i, ⌜a = .ok i⌝ ∗ □ allocIfaceM i
def isMapV_methods.law : Prop :=
  ∀ m kvs, isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isMapV m kvs ⊢
    isMapV m kvs ∗ ∃ i, ⌜m = .ok i⌝ ∗ □ mapIfaceM i
def isListV_methods.law : Prop :=
  ∀ l vs, isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ isListV l vs ⊢
    isListV l vs ∗ ∃ i, ⌜l = .ok i⌝ ∗ □ listIfaceM i
def ownRange_methods.law : Prop :=
  ∀ r vs n, isPkgInit (PROP := IProp GF) pkg_id.sigs_k8s_io.structured_merge_diff.v7.value ∗ ownRange r vs n ⊢
    ownRange r vs n ∗ ∃ i, ⌜r = .ok i⌝ ∗ □ rangeIfaceM i

/-- **`value.Compare` is a strict total order on canonical values, zero exactly on equal ones**
(requested by `fieldpath`'s Draft: `PathElement.Compare`'s order rests on it). -/
def UVal.compare_eq_zero.law : Prop :=
  ∀ a b : UVal, a.canon = true → b.canon = true → (UVal.compare a b = 0 ↔ a = b)
def UVal.compare_antisymm.law : Prop :=
  ∀ a b : UVal, a.canon = true → b.canon = true → (UVal.compare a b < 0 ↔ 0 < UVal.compare b a)
def UVal.compare_trans.law : Prop :=
  ∀ a b c : UVal, a.canon = true → b.canon = true → c.canon = true →
    UVal.compare a b < 0 → UVal.compare b c < 0 → UVal.compare a c < 0
/-- An interface's value is canonical (`isIface`'s maps are sorted). -/
def isValF_canon.law : Prop := ∀ v dq x, isValF (GF := GF) v dq x ⊢ ⌜x.canon = true⌝
/-- Agreement of a `FieldList` (requested by `fieldpath`'s Draft). -/
def isFieldList_agree.law : Prop :=
  ∀ s a b, isFieldList (GF := GF) s a ∗ isFieldList s b ⊢ ⌜a = b⌝

/-- **The dynamic types in scope** (the Draft's integration, 2026-11-19): a proof calling a method
of one of `value`'s interfaces resolves its dynamic type with these and takes the concrete
method's spec (`<T>.<M>`, or `<T>.<M>_ptr` for a pointer to a value receiver) as a hypothesis, as
`fieldpath`'s `isVSet_concrete`; the bundles above (`*_methods`) are what a client outside the
package may use instead. -/
def isValF_concrete.law : Prop :=
  ∀ v dq x, isValF (GF := GF) v dq x ⊢
    ∃ p : Loc, ⌜v = interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #p⌝
def isMapV_concrete.law : Prop :=
  ∀ m kvs, isMapV (GF := GF) m kvs ⊢ ∃ gm : GoMap, ⌜m = interface.mkOk value.mapUnstructuredString.ty #gm⌝
def isListV_concrete.law : Prop :=
  ∀ l vs, isListV (GF := GF) l vs ⊢
    (∃ sl : GoSlice, ⌜l = interface.mkOk value.listUnstructured.ty #sl⌝) ∨
    (∃ p : Loc, ⌜l = interface.mkOk (go.GoType.PointerType value.listUnstructured.ty) #p⌝)
def ownRange_concrete.law : Prop :=
  ∀ r vs n, ownRange (GF := GF) r vs n ⊢ ownRange r vs n ∗
    ((∃ q : Loc, ⌜r = interface.mkOk (go.GoType.PointerType value.emptyRange.ty) #q⌝) ∨
     (∃ q : Loc, ⌜r = interface.mkOk (go.GoType.PointerType value.listUnstructuredRange.ty) #q⌝))
def isAlloc_concrete.law : Prop :=
  ∀ a, isAlloc (GF := GF) a ⊢ isAlloc a ∗
    ((∃ p : Loc, ⌜a = interface.mkOk (go.GoType.PointerType value.heapAllocator.ty) #p⌝) ∨
     (∃ p : Loc, ⌜a = interface.mkOk (go.GoType.PointerType value.freelistAllocator.ty) #p⌝))

/-- The pure facts the zips' clients use. -/
def zipKeys_nodup.law : Prop :=
  ∀ ol or_, (∀ kvs, ol = some kvs → keysSorted kvs = true) →
    (∀ kvs, or_ = some kvs → keysSorted kvs = true) → (zipKeys ol or_).Nodup
def zipKeys_mem.law : Prop :=
  ∀ ol or_ k, k ∈ zipKeys ol or_ ↔
    ((lookupKV k (kvsOrEmpty ol)).isSome ∨ (lookupKV k (kvsOrEmpty or_)).isSome)

end laws

end smd
end EtcdGrove
end Perennial
