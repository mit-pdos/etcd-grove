/-
**structured-merge-diff's values, abstractly** (`value` package, v7.0.0): the vocabulary of the
SMD API specs (`notes/smd-plan.md`, "The vocabulary").

`UVal` is an unstructured value as SMD sees it through `value.NewValueInterface`: `null`, a `bool`,
an `int64`, a `string`, a list, a map from strings. A map is kept **canonical**: its entries sorted
by key (bytewise, `strings.Compare`), no key twice (`UVal.Canonical`), so that two maps with the
same entries are the same `UVal` and `value.Equals` is `=`. Out of scope (the representation
predicate `isIface` admits none): floats (SMD compares an `int64` with a `float64` by converting:
SSA-05), the other integer types, `map[interface{}]interface{}`, reflection-backed values.

The representation predicates are persistent: SMD never writes a value it was given or returned,
and a caller gives up its literals for reading (discarded fractions).

Lean-first (2026-11-19, notes/smd-plan.md).
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

/-- The value of key `k` in an association list. -/
def lookupKV {α : Type} (k : GoString) : List (GoString × α) → Option α
  | [] => none
  | (k', v) :: rest => if k' = k then some v else lookupKV k rest

/-- The keys are strictly increasing (`gsLt`). -/
def keysSorted {α : Type} : List (GoString × α) → Bool
  | [] => true
  | [_] => true
  | (k, _) :: (k', v') :: rest => gsLt k k' && keysSorted ((k', v') :: rest)

mutual
/-- Every map in the value is canonical (`keysSorted`). -/
def UVal.Canonical : UVal → Prop
  | .list vs => UVal.CanonicalL vs
  | .map kvs => keysSorted kvs = true ∧ UVal.CanonicalM kvs
  | _ => True
def UVal.CanonicalL : List UVal → Prop
  | [] => True
  | v :: vs => UVal.Canonical v ∧ UVal.CanonicalL vs
def UVal.CanonicalM : List (GoString × UVal) → Prop
  | [] => True
  | (_, v) :: kvs => UVal.Canonical v ∧ UVal.CanonicalM kvs
end

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
keys are exactly `x`'s, `x` canonical). -/
def isIface (i : GoInterface) : UVal → IProp GF
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
/-- A list's items. -/
def isIfaceL : List GoInterface → List UVal → IProp GF
  | [], [] => iprop(True)
  | x :: xs, v :: vs => iprop(isIface x v ∗ isIfaceL xs vs)
  | _, _ => iprop(False)
  termination_by structural _ vs => vs
/-- A map's entries. -/
def isIfaceM (M : GMap GoString GoInterface) : List (GoString × UVal) → IProp GF
  | [] => iprop(True)
  | (k, v) :: kvs => iprop(∃ x, ⌜M !! k = some x⌝ ∗ isIface x v ∗ isIfaceM M kvs)
  termination_by structural kvs => kvs
end

/-- **`isVal v x`**: the `value.Value` `v` is a value built by `NewValueInterface` (a
`*valueUnstructured`) over an interface holding `x` (persistent). -/
def isVal (v : value.Value) (x : UVal) : IProp GF :=
  iprop(∃ (p : Loc) (i : GoInterface),
    ⌜v = interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #p⌝ ∗
    p ↦□ (value.valueUnstructured.mk i) ∗ isIface i x)

end own

end smd
end EtcdGrove
end Perennial
