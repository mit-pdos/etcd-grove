/-
**structured-merge-diff's values, abstractly** (`value` package, v7.0.0): the vocabulary of the
SMD API specs (`notes/smd-plan.md`, "The vocabulary").

`UVal` is an unstructured value as SMD sees it through `value.NewValueInterface`: `null`, a `bool`,
an `int64`, a `string`, a list, a map from strings. A map is kept **canonical**: its entries sorted
by key (bytewise, `strings.Compare`), no key twice (`keysSorted`; `UVal.ofMap` sorts a literal's entries), so that two maps with the
same entries are the same `UVal` and `value.Equals` is `=`. Out of scope (the representation
predicate `isIface` admits none): floats (SMD compares an `int64` with a `float64` by converting:
SSA-05), the other integer types, `map[interface{}]interface{}`, reflection-backed values.

The pure vocabulary is **computable** (review round 1, P1): `UVal` has a hand-written `DecidableEq`
(Lean's deriving handler fails on the nested `List (GoString × UVal)`), so a client decides an
equality of literals by `decide` (the kernel's, structural recursion only).

`isValF v dq x` is a `value.Value` wrapper at fraction `dq` (SMD's own recursion lends wrappers it
rewrites: `reuse`, the freelist allocator); `isVal v x`, its instance at `DFrac.discard`, is what
the API hands out and takes (persistent: SMD never writes a value it was given or returned). The
representation's internals (`isIface`'s list and map parts) are sealed (`@[no_expose]`); clients
use the laws (`Laws.lean`).

Scope restrictions of the representation (`notes/smd-plan.md`, "Scope", (R)): a map is a non-nil
`map[string]interface{}` (Go's typed-nil map, which SMD reads as `{}`, is not admitted); recursion
depth: SMD recurses once per level of a value, and Go's 1 GB stack bounds the depth where
GooseLang's semantics has no bound (the margin of every post over a value: `notes/smd-plan.md`,
"Margins").

Lean-first (2026-11-19, notes/smd-plan.md); round 1's repairs 2026-11-19.
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI
open sigs_k8s_io.structured_merge_diff.v7

/-! ## Pure values -/

/-- `strings.Compare`: bytewise. -/
def gsCompare : GoString → GoString → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | x :: xs, y :: ys =>
    if x.toNat < y.toNat then -1 else if y.toNat < x.toNat then 1 else gsCompare xs ys

/-- `a < b` as Go compares strings. -/
def gsLt (a b : GoString) : Bool := gsCompare a b == -1

/-- An unstructured value (see the file header). -/
inductive UVal where
  | null
  | bool (b : Bool)
  | int (i : w64)
  | str (s : GoString)
  | list (vs : List UVal)
  | map (kvs : List (GoString × UVal))
  deriving Inhabited

mutual
/-- Equality of values, decided (by structural recursion, so that the kernel evaluates it). -/
def UVal.decEq : (a b : UVal) → Decidable (a = b)
  | .null, .null => isTrue rfl
  | .bool a, .bool b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .int a, .int b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .str a, .str b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .list a, .list b => match UVal.decEqL a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .map a, .map b => match UVal.decEqM a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .null, .bool _ | .null, .int _ | .null, .str _ | .null, .list _ | .null, .map _
  | .bool _, .null | .bool _, .int _ | .bool _, .str _ | .bool _, .list _ | .bool _, .map _
  | .int _, .null | .int _, .bool _ | .int _, .str _ | .int _, .list _ | .int _, .map _
  | .str _, .null | .str _, .bool _ | .str _, .int _ | .str _, .list _ | .str _, .map _
  | .list _, .null | .list _, .bool _ | .list _, .int _ | .list _, .str _ | .list _, .map _
  | .map _, .null | .map _, .bool _ | .map _, .int _ | .map _, .str _ | .map _, .list _ =>
    isFalse (fun e => by cases e)
/-- Lists of values. -/
def UVal.decEqL : (a b : List UVal) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
  | x :: xs, y :: ys => match UVal.decEq x y, UVal.decEqL xs ys with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h1, _ => isFalse (fun e => by cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
/-- Maps' entries. -/
def UVal.decEqM : (a b : List (GoString × UVal)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
  | (k, x) :: xs, (k', y) :: ys =>
    if hk : k = k' then
      match UVal.decEq x y, UVal.decEqM xs ys with
      | isTrue h1, isTrue h2 => isTrue (hk ▸ h1 ▸ h2 ▸ rfl)
      | isFalse h1, _ => isFalse (fun e => by cases e; exact h1 rfl)
      | _, isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
    else isFalse (fun e => by cases e; exact hk rfl)
end

instance : DecidableEq UVal := UVal.decEq

/-- The value of key `k` in an association list. -/
def lookupKV {α : Type} (k : GoString) : List (GoString × α) → Option α
  | [] => none
  | (k', v) :: rest => if k' = k then some v else lookupKV k rest

/-- The keys are strictly increasing (`gsLt`). -/
def keysSorted {α : Type} : List (GoString × α) → Bool
  | [] => true
  | [_] => true
  | (k, _) :: (k', v') :: rest => gsLt k k' && keysSorted ((k', v') :: rest)

/-- `m[k] = v` on a map kept sorted by key (`gsLt`): replaces `k`'s entry, else inserts it in
order. -/
def insertKV {α : Type} (k : GoString) (v : α) : List (GoString × α) → List (GoString × α)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k' = k then (k, v) :: rest
    else if gsLt k k' then (k, v) :: (k', v') :: rest
    else (k', v') :: insertKV k v rest

/-- **A Go map literal's entries**, sorted, the last assignment of a key winning (`map[K]V{...}`
written in any order; the canonical association list `isIface`'s maps and `MF` use). -/
def kvsOf {α : Type} (kvs : List (GoString × α)) : List (GoString × α) :=
  kvs.foldl (fun m (k, v) => insertKV k v m) []

/-- **`UVal.ofMap kvs`**: the map value of a `map[string]interface{}` literal with the entries
`kvs` (any order; sorted here). -/
def UVal.ofMap (kvs : List (GoString × UVal)) : UVal := .map (kvsOf kvs)

mutual
/-- The size of a value (a measure for the fuelled definitions of `typed/Defs.lean`). -/
def UVal.size : UVal → Nat
  | .list vs => UVal.sizeL vs + 1
  | .map kvs => UVal.sizeM kvs + 1
  | _ => 1
def UVal.sizeL : List UVal → Nat
  | [] => 0
  | v :: vs => UVal.size v + UVal.sizeL vs
def UVal.sizeM : List (GoString × UVal) → Nat
  | [] => 0
  | (_, v) :: kvs => UVal.size v + UVal.sizeM kvs
end

/-- `value.IntCompare`. -/
def intCompare (a b : w64) : Int :=
  if a.toInt > b.toInt then 1 else if a.toInt == b.toInt then 0 else -1

/-- `value.BoolCompare`. -/
def boolCompare (a b : Bool) : Int :=
  if a == b then 0 else if !a then -1 else 1

/-- The keys of two canonical maps in order, with each side's value (`MapZip` in lexical order). -/
def zipLexical (fuel : Nat) (xs ys : List (GoString × UVal)) :
    List (GoString × Option UVal × Option UVal) :=
  match fuel, xs, ys with
  | 0, _, _ => []
  | _ + 1, [], [] => []
  | _ + 1, (k, a) :: xs, [] => (k, some a, none) :: xs.map (fun (k, a) => (k, some a, none))
  | _ + 1, [], (k, b) :: ys => (k, none, some b) :: ys.map (fun (k, b) => (k, none, some b))
  | n + 1, (k, a) :: xs', (k', b) :: ys' =>
    if k = k' then (k, some a, some b) :: zipLexical n xs' ys'
    else if gsLt k k' then (k, some a, none) :: zipLexical n xs' ((k', b) :: ys')
    else (k', none, some b) :: zipLexical n ((k, a) :: xs') ys'

/-- `value.Compare` (on values without floats), with fuel (`size a + size b + 1` suffices). It is
the order of the path elements in a `fieldpath.Set`'s sorted slices (`fieldpath/Defs.lean`,
`PE.compare`), so it appears only in the representation of sets, which clients never unfold. -/
def UVal.compareF : Nat → UVal → UVal → Int
  | 0, _, _ => 0
  | n + 1, lhs, rhs =>
    match lhs, rhs with
    | .int a, .int b => intCompare a b
    | .int _, _ => -1
    | _, .int _ => 1
    | .str a, .str b => gsCompare a b
    | .str _, _ => -1
    | _, .str _ => 1
    | .bool a, .bool b => boolCompare a b
    | .bool _, _ => -1
    | _, .bool _ => 1
    | .list xs, .list ys =>
      let r := (xs.zip ys).foldl (fun c (a, b) => if c != 0 then c else UVal.compareF n a b) 0
      if r != 0 then r else if xs.length < ys.length then -1 else if ys.length < xs.length then 1 else 0
    | .list _, _ => -1
    | _, .list _ => 1
    | .map xs, .map ys =>
      if xs.length == 0 && ys.length == 0 then 0 else
      let z := zipLexical (xs.length + ys.length + 1) xs ys
      let step : (Int × Nat × Bool) → (GoString × Option UVal × Option UVal) → (Int × Nat × Bool) :=
        fun (c, i, stop) (_, l, r) =>
          if stop then (c, i, stop) else
          let c :=
            if i == xs.length then -1
            else if i == ys.length then 1
            else match l, r with
              | none, _ => 1
              | _, none => -1
              | some l, some r => UVal.compareF n l r
          (c, i + 1, c != 0)
      (z.foldl step (0, 0, false)).1
    | .map _, _ => -1
    | _, .map _ => 1
    | .null, .null => 0

/-- `value.Compare`. -/
def UVal.compare (a b : UVal) : Int := UVal.compareF (a.size + b.size + 1) a b

/-! ## Representation predicates -/

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `interface{}`. -/
abbrev ifaceTy : go.GoType := go.GoType.InterfaceType []
/-- `map[string]interface{}`. -/
abbrev mapStrIfaceTy : go.GoType := go.GoType.MapType go.string ifaceTy
/-- `[]interface{}`. -/
abbrev sliceIfaceTy : go.GoType := go.GoType.SliceType ifaceTy

mutual
/-- **`isIface i x`**: the `interface{}` `i` holds the unstructured value `x` (persistent): `nil`, a
`bool`, an `int64`, a `string`, a `[]interface{}` or a non-nil `map[string]interface{}` (whose
keys are exactly `x`'s, `x`'s entries sorted). Sealed: clients use the laws. -/
@[no_expose] def isIface (i : GoInterface) : UVal → IProp GF
  | .null => iprop(⌜i = interface.nil⌝)
  | .bool b => iprop(⌜i = interface.mkOk go.bool #b⌝)
  | .int n => iprop(⌜i = interface.mkOk go.int64 #n⌝)
  | .str s => iprop(⌜i = interface.mkOk go.string #s⌝)
  | .list vs => iprop(∃ (sl : GoSlice) (xs : List GoInterface),
      ⌜i = interface.mkOk sliceIfaceTy #sl⌝ ∗ sl ↦*{DFrac.discard} xs ∗ isIfaceL xs vs)
  | .map kvs => iprop(∃ (m : GoMap) (M : GMap GoString GoInterface),
      ⌜i = interface.mkOk mapStrIfaceTy #m⌝ ∗ m ↦$□ M ∗
      ⌜keysSorted kvs = true ∧ ∀ k, (M !! k).isSome = (lookupKV k kvs).isSome⌝ ∗ isIfaceM M kvs)
  termination_by structural x => x
/-- A list's items (internal). -/
@[no_expose] def isIfaceL : List GoInterface → List UVal → IProp GF
  | [], [] => iprop(True)
  | x :: xs, v :: vs => iprop(isIface x v ∗ isIfaceL xs vs)
  | _, _ => iprop(False)
  termination_by structural _ vs => vs
/-- A map's entries (internal). -/
@[no_expose] def isIfaceM (M : GMap GoString GoInterface) : List (GoString × UVal) → IProp GF
  | [] => iprop(True)
  | (k, v) :: kvs => iprop(∃ x, ⌜M !! k = some x⌝ ∗ isIface x v ∗ isIfaceM M kvs)
  termination_by structural kvs => kvs
end

/-- **`isValF v dq x`**: the `value.Value` `v` is a value built by `NewValueInterface` (a
`*valueUnstructured`), its wrapper owned at fraction `dq`, over an interface holding `x`. A
fraction (or the whole wrapper) is what SMD's own recursion lends: `EqualsUsing`'s map case
rewrites one wrapper per entry (`reuse`), the freelist allocator frees and reuses them. Sealed. -/
@[no_expose] def isValF (v : value.Value) (dq : DFrac) (x : UVal) : IProp GF :=
  iprop(∃ (p : Loc) (i : GoInterface),
    ⌜v = interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #p⌝ ∗
    p ↦{dq} (value.valueUnstructured.mk i) ∗ isIface i x)

/-- **`isVal v x`**: `isValF` at the discarded fraction: a value the API takes or hands out
(persistent: SMD never writes a value it was given or returned). -/
abbrev isVal (v : value.Value) (x : UVal) : IProp GF := isValF v DFrac.discard x

end own

end smd
end EtcdGrove
end Perennial
